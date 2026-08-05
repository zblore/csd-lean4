/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF1.MainTheorem
public import CsdLean4.LF1.GeneralFrequency
public import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvex
public import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvexBridge
public import CsdLean4.Mathlib.Analysis.Matrix.StoneC1
public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound
public import CsdLean4.LF2.BornWrapper
public import CsdLean4.LF2.ReducedDensity
public import CsdLean4.LF2.QuantumChannel
public import CsdLean4.Mathlib.MeasureTheory.LintegralFintypeProd
public import CsdLean4.Mathlib.QuantumInfo.Channel
public import CsdLean4.Mathlib.QuantumInfo.Stinespring
public import CsdLean4.Mathlib.QuantumInfo.CanonicalChannels
public import CsdLean4.Mathlib.QuantumInfo.TraceDistance
public import CsdLean4.Mathlib.QuantumInfo.DataProcessing
public import CsdLean4.Mathlib.QuantumInfo.Helstrom
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
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMul
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop
public import CsdLean4.Mathlib.QuantumInfo.Reversible.VerifiedAdder
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularSub
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularConst
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Depth
public import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModMul
public import CsdLean4.Mathlib.QuantumInfo.Reversible.VerifiedAdderCarryClean
public import CsdLean4.Mathlib.QuantumInfo.Reversible.AndAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.GidneyAdder
public import CsdLean4.Empirical.QM.MeasurementUncompute
public import CsdLean4.Empirical.QM.MeasurementUncomputeLift
public import CsdLean4.Empirical.QM.MeasurementAdder
public import CsdLean4.Empirical.QM.MeasurementGidneyAdder
public import CsdLean4.Empirical.QM.MeasurementAdderHierarchy
public import CsdLean4.CV.ApproxCCR
public import CsdLean4.CV.Position
public import CsdLean4.CV.Oscillator
public import CsdLean4.CV.OscillatorSpectrum
public import CsdLean4.CV.OscillatorBorn
public import CsdLean4.CV.FieldModes
public import CsdLean4.CV.Dispersion
public import CsdLean4.CV.ModeLocality
public import CsdLean4.Thermo.CanonicalTypicality
public import CsdLean4.Thermo.SecondLaw
public import CsdLean4.Thermo.FreeEnergy
public import CsdLean4.Thermo.Landauer
public import CsdLean4.LF2.Interface
public import CsdLean4.LF2.Preparation
public import CsdLean4.LF3.Interface
public import CsdLean4.LF3.PurePreparation
public import CsdLean4.LF3.SingletProjective
public import CsdLean4.LF3.Singlet.JointProjector
public import CsdLean4.LF3.Singlet.JointEig
public import CsdLean4.LF3.Projectors.TensorModel
public import CsdLean4.LF4.Instance
public import CsdLean4.LF4.KahlerInstance
public import CsdLean4.LF4.KahlerFlow
public import CsdLean4.LF4.KahlerOnticSetup
public import CsdLean4.LF4.NonTrivialSetup
public import CsdLean4.LF4.RotationSchrodinger
public import CsdLean4.LF4.BothPillars
public import CsdLean4.LF4.ManyToOnePillars
public import CsdLean4.LF4.ManyToOneSchrodingerDerived
public import CsdLean4.LF4.UnitarySelection
public import CsdLean4.LF4.BargmannSelection
public import CsdLean4.LF4.ProjectedDynamics
public import CsdLean4.LF4.PhaseLift
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.PhaseRigidity
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Bargmann
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
public import CsdLean4.LF4.MomentRatioUniform
public import CsdLean4.LF4.MomentRatioUniformN
public import CsdLean4.LF4.MomentUniform
public import CsdLean4.LF4.HatBox
public import CsdLean4.LF4.QubitReflection
public import CsdLean4.LF4.BlochProjection
public import CsdLean4.LF4.AxisBridge
public import CsdLean4.LF4.QubitDipole
public import CsdLean4.LF4.QubitCrossTerm
public import CsdLean4.LF4.QubitBorn
public import CsdLean4.LF4.MomentBridgeN
public import CsdLean4.LF4.MomentDirichletN
public import CsdLean4.LF4.MomentBornN
public import CsdLean4.LF4.ObservableCorrespondenceN
public import CsdLean4.Empirical.CSD.MixedStateBornVolume
public import CsdLean4.Empirical.CSD.SequentialMeasurement
public import CsdLean4.Empirical.CSD.Contextuality.KCBSVolume
public import CsdLean4.Empirical.CSD.QuantumEraserVolume
public import CsdLean4.SigmaLayer.RotatedContext
public import CsdLean4.Empirical.CSD.Crypto.BB84Sequential
public import CsdLean4.Empirical.CSD.Crypto.B92Sequential
public import CsdLean4.Empirical.CSD.Crypto.WiesnerSequential
public import CsdLean4.SigmaLayer.ShearDiscontinuity
public import CsdLean4.SigmaLayer.PiecewiseHamiltonian
public import CsdLean4.SigmaLayer.SwapClosure
public import CsdLean4.SigmaLayer.UnifiedArena
public import CsdLean4.SigmaLayer.BlockCollapse
public import CsdLean4.SigmaLayer.PhaseSlot
public import CsdLean4.SigmaLayer.JoinArena
public import CsdLean4.SigmaLayer.JoinProtocol
public import CsdLean4.SigmaLayer.JoinLuders
public import CsdLean4.SigmaLayer.RotatedSwap
public import CsdLean4.SigmaLayer.PointerArena
public import CsdLean4.SigmaLayer.PointerRotation
public import CsdLean4.SigmaLayer.PointerCoupling
public import CsdLean4.SigmaLayer.PointerWeights
public import CsdLean4.SigmaLayer.PointerLanding
public import CsdLean4.SigmaLayer.PointerProtocol
public import CsdLean4.SigmaLayer.PointerBorn
public import CsdLean4.SigmaLayer.PointerGeneration
public import CsdLean4.SigmaLayer.LocalLuders
public import CsdLean4.SigmaLayer.LocalBlockBridge
public import CsdLean4.SigmaLayer.LocalLudersBasis
public import CsdLean4.Empirical.CSD.EraserDynamics
public import CsdLean4.Empirical.CSD.EraserSequential
public import CsdLean4.SigmaLayer.MeasurementCapstone
public import CsdLean4.SigmaLayer.MixedSwap
public import CsdLean4.SigmaLayer.PovmDynamics
public import CsdLean4.SigmaLayer.JoinClosure
public import CsdLean4.SigmaLayer.MixedLuders
public import CsdLean4.SigmaLayer.PointerSmoothProfile
public import CsdLean4.SigmaLayer.NullSeamWitness
public import CsdLean4.SigmaLayer.JointFlowTransfer
public import CsdLean4.SigmaLayer.ChartBracket
public import CsdLean4.SigmaLayer.NullSeamLift
public import CsdLean4.SigmaLayer.PointerFrequency
public import CsdLean4.SigmaLayer.PovmSectorBorn
public import CsdLean4.SigmaLayer.SharpenedNoGo
public import CsdLean4.SigmaLayer.PointerLuders
public import CsdLean4.SigmaLayer.NoRecordGeometry
public import CsdLean4.LF4.BornFrequencyN
public import CsdLean4.LF4.QubitConsistency
public import CsdLean4.Mathlib.MeasureTheory.PiCurry
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
public import CsdLean4.LF2.POVM
public import CsdLean4.LF2.EffectAux
public import CsdLean4.LF4.POVMDilation
public import CsdLean4.LF4.POVMVolume
public import CsdLean4.LF4.BornFlowLinkage
public import CsdLean4.LF4.POVMNaimark
public import CsdLean4.LF4.BornRegionUncond
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
public import CsdLean4.Empirical.QM.LeggettGarg
public import CsdLean4.Empirical.QM.QuantumEraser
public import CsdLean4.Empirical.QM.ElitzurVaidman
public import CsdLean4.Empirical.QM.KCBS
public import CsdLean4.Empirical.QM.HongOuMandel
public import CsdLean4.Empirical.QM.NoCloning
public import CsdLean4.Empirical.QM.NoDeleting
public import CsdLean4.Empirical.QM.Resources.SuperdenseCoding
public import CsdLean4.Empirical.QM.Resources.Teleportation
public import CsdLean4.Empirical.QM.NoCommunication
public import CsdLean4.Empirical.QM.NoBroadcasting
public import CsdLean4.Empirical.QM.Protocols.Basic
public import CsdLean4.Empirical.QM.Crypto.QuantumMoney
public import CsdLean4.Empirical.QM.Crypto.BB84
public import CsdLean4.Empirical.QM.Crypto.B92
public import CsdLean4.Empirical.QM.Crypto.E91
public import CsdLean4.Empirical.QM.Crypto.E91KeyRate
public import CsdLean4.Empirical.QM.Crypto.E91FiniteKey
public import CsdLean4.Empirical.QM.Crypto.WiesnerProtocol
public import CsdLean4.Empirical.QM.USD
public import CsdLean4.Empirical.QM.QEC.ThreeQubit
public import CsdLean4.Empirical.QM.QEC.PhaseFlip
public import CsdLean4.Empirical.QM.QEC.ErrorDiscretization
public import CsdLean4.Empirical.QM.QEC.SyndromeCollapse
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
public import CsdLean4.Empirical.CSD.MalusVolume
public import CsdLean4.Empirical.CSD.LeggettGargVolume
public import CsdLean4.Empirical.CSD.ElitzurVaidmanVolume
public import CsdLean4.Empirical.CSD.HongOuMandelVolume
public import CsdLean4.Empirical.Metrology.Ramsey
public import CsdLean4.Empirical.CSD.MachZehnderVolume
public import CsdLean4.Empirical.CSD.DoubleSlitVolume
public import CsdLean4.Empirical.Metrology.QuantumFisher
public import CsdLean4.Empirical.Metrology.Heisenberg
public import CsdLean4.Empirical.CSD.BellVolume
public import CsdLean4.Empirical.CSD.GHZVolume
public import CsdLean4.Empirical.CSD.HardyVolume
public import CsdLean4.Empirical.CSD.ContextVolume
public import CsdLean4.Empirical.CSD.UncertaintyVolume
public import CsdLean4.Empirical.CSD.TrineVolume
public import CsdLean4.Empirical.CSD.USDVolume
public import CsdLean4.Empirical.CSD.SICVolume
public import CsdLean4.Empirical.CSD.WeakMeasurement
public import CsdLean4.Empirical.CSD.QuantumZeno
public import CsdLean4.Empirical.CSD.QutritPOVMVolume
public import CsdLean4.Empirical.CSD.SIC3Volume
public import CsdLean4.Empirical.CSD.MUB3Volume
public import CsdLean4.Empirical.CSD.VolumeCanonical
public import CsdLean4.Empirical.CSD.Resources.SuperdenseCoding
public import CsdLean4.Empirical.CSD.Resources.Teleportation
public import CsdLean4.Empirical.CSD.Crypto.QuantumMoney
public import CsdLean4.Empirical.CSD.Crypto.E91
public import CsdLean4.Empirical.CSD.QEC.ThreeQubit
public import CsdLean4.Empirical.CSD.Contextuality.MerminPeres
public import CsdLean4.Empirical.CSD.Hardy
public import CsdLean4.Empirical.CSD.Contextuality.KS18
public import CsdLean4.Empirical.CSD.Contextuality.KS18Volume
public import CsdLean4.Empirical.CSD.Contextuality.MerminPeresVolume
public import CsdLean4.Empirical.CSD.Multipartite.GHZ
public import CsdLean4.Empirical.CSD.Einselection
public import CsdLean4.Empirical.CSD.QECDecoherence
public import CsdLean4.Empirical.CSD.ChannelCapacity
public import CsdLean4.Empirical.QM.Gates.SingleQubit
public import CsdLean4.Empirical.QM.Gates.TwoQubit
public import CsdLean4.Empirical.QM.Gates.BellPrep
public import CsdLean4.Empirical.QM.Gates.MultiQubit
public import CsdLean4.Empirical.CSD.Gates.Framework
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Unitary
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryCompact
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryHaar
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerForm
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
public import CsdLean4.Empirical.CSD.Gates.WignerDischarge
public import CsdLean4.Empirical.CSD.Gates.SingleQubitDischarge
public import CsdLean4.Empirical.CSD.Gates.TwoQubitDischarge
public import CsdLean4.Empirical.CSD.Gates.MultiQubitDischarge
public import CsdLean4.Empirical.CSD.Gates.BellPrepDischarge
public import CsdLean4.Mathlib.Probability.CGLMP
public import CsdLean4.SigmaLayer.Adapters
public import CsdLean4.SigmaLayer.ForwardCapstone
public import CsdLean4.SigmaLayer.LiftedMeasurement
public import CsdLean4.SigmaLayer.UnifiedMeasurement
public import CsdLean4.SigmaLayer.UnifiedFlowedRecords
public import CsdLean4.SigmaLayer.FiniteQMClosure
public import CsdLean4.SigmaLayer.ConditioningLink
public import CsdLean4.SigmaLayer.ConditioningLuders
public import CsdLean4.SigmaLayer.PostMeasurement
public import CsdLean4.SigmaLayer.TimeIndexedRecord
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
public import CsdLean4.SigmaLayer.MixedEnsemble
public import CsdLean4.LF2.MixedEnsembleIx
public import CsdLean4.LF2.ChoiConverse
public import CsdLean4.SigmaLayer.MixedOntic
public import CsdLean4.SigmaLayer.MixedFrequency
public import CsdLean4.SigmaLayer.Symmetrization
public import CsdLean4.SigmaLayer.OnticBornFrequency
public import CsdLean4.SigmaLayer.BornFibrePartition
public import CsdLean4.SigmaLayer.DeIsolationFlow
public import CsdLean4.SigmaLayer.FibreRecord
public import CsdLean4.SigmaLayer.RecordLayerClosure
public import CsdLean4.SigmaLayer.ContextFixedA7
public import CsdLean4.SigmaLayer.ContextFixedA7FS
public import CsdLean4.SigmaLayer.CircleFibre
public import CsdLean4.SigmaLayer.CircleRecord
public import CsdLean4.SigmaLayer.TorusFibre
public import CsdLean4.SigmaLayer.GlobalBasin
public import CsdLean4.SigmaLayer.GlobalRecordClosure
public import CsdLean4.SigmaLayer.MeasurementConstraints
public import CsdLean4.SigmaLayer.MeasurementProtocol
public import CsdLean4.SigmaLayer.RecordPersistence
public import CsdLean4.SigmaLayer.ShearWitness
public import CsdLean4.SigmaLayer.DynamicBorn
public import CsdLean4.SigmaLayer.OutcomeField
public import CsdLean4.SigmaLayer.OutcomeBasin
public import CsdLean4.SigmaLayer.DynamicMeasurementClosure
public import CsdLean4.Mathlib.MeasureTheory.PiecewisePreserving
public import CsdLean4.SigmaLayer.SwapWitness
public import CsdLean4.SigmaLayer.SwapLuders
public import CsdLean4.SigmaLayer.DegenerateLuders
public import CsdLean4.SigmaLayer.ApproxProjectability
public import CsdLean4.SigmaLayer.HamiltonianSignature
public import CsdLean4.SigmaLayer.OnticComposite
public import CsdLean4.SigmaLayer.OnticMarginals
public import CsdLean4.SigmaLayer.MomentMapRace
public import CsdLean4.SigmaLayer.Measurement
public import CsdLean4.SigmaLayer.ProjectiveRecord
public import CsdLean4.SigmaLayer.FibredSigma
public import CsdLean4.SigmaLayer.BasisMeasurement
public import CsdLean4.SigmaLayer.KSigmaRecord

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

@[expose] public section

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
-- `cp_measure_bridge` / `k_measure_bridge`, pinned below. `busch_effect_gleason` was the
-- last imported axiom; it was DISCHARGED 2026-07-21 — see below — so the corpus now imports
-- ZERO axioms beyond the foundational triple.)
/-- info: 'CSD.LF2.born_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms born_quadratic

-- QuantumChannel (general CPTP maps, 2026-07-18): channels in Kraus form (∑ₖ Kₖ†Kₖ=1). T1 CPTP-forward:
-- channelApply sends density operators to density operators (apply_posSemidef via mul_mul_conjTranspose_same
-- + posSemidef_sum; apply_trace via trace cyclicity + the constraint), unitaryChannel, comp (channels
-- compose). T2 Stinespring: dilation_isometry (V†V=1) + stinespring (Φ(ρ) = Tr_E(VρV†) via partialTraceRight).
-- T3 Choi: choiMatrix_posSemidef (the Choi-Jamiolkowski completely-positive witness, ∑ₖ vec(Kₖ)vec(Kₖ)† PSD).
-- T4 Choi converse (ChoiConverse.lean, 2026-07-19): choi_iff_posSemidef — a matrix on Fin M × Fin N is the
-- Choi matrix of some Kraus family iff it is PSD; choiOfKraus_krausOfChoi reconstructs the family Kᵢ=√λᵢ·unvec(eᵢ)
-- from the spectral decomposition (IsHermitian.eq_eigen_outer). Closes Choi's theorem (CP ⟺ PSD Choi).
/-- info: 'CSD.LF2.QuantumChannel.channelApply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.channelApply

/-- info: 'CSD.LF2.QuantumChannel.apply_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.apply_trace

/-- info: 'CSD.LF2.QuantumChannel.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.comp

/-- info: 'CSD.LF2.QuantumChannel.dilation_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.dilation_isometry

/-- info: 'CSD.LF2.QuantumChannel.stinespring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.stinespring

/-- info: 'CSD.LF2.QuantumChannel.choiMatrix_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.QuantumChannel.choiMatrix_posSemidef

/-- info: 'CSD.LF2.IsHermitian.eq_eigen_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.IsHermitian.eq_eigen_outer

/-- info: 'CSD.LF2.choiOfKraus_krausOfChoi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.choiOfKraus_krausOfChoi

/-- info: 'CSD.LF2.choi_iff_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.choi_iff_posSemidef

-- Partial trace (Cat-1 Mathlib staging) + the reduced density operator (LF2).
-- traceRight/traceLeft trace out a tensor factor; the API (kronecker defining
-- property, trace-preservation, Hermitian/PSD preservation) sends a density
-- operator to its reduced density operator. Foundational triple. Unblocks E3b/E2.
-- (2026-07-20 Mathlib v4.33 upgrade: traceRight_kronecker gained Classical.choice — a
-- transitively-used Mathlib lemma became classical upstream; still the foundational triple.)
/-- info: 'Matrix.traceRight_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

-- `busch_effect_gleason` discharged 2026-07-21: this is now foundational-triple only.
/-- info: 'CSD.LF2.pure_state_born_weights_of_certainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pure_state_born_weights_of_certainty

/-- info: 'CSD.LF2.PurePreparation.OP_certain_at_ψ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.OP_certain_at_ψ

/-- info: 'CSD.LF2.PurePreparation.born_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

-- Leggett–Garg inequality (temporal CHSH / macrorealism test, 2026-07-26): the macrorealist bound
-- K₃ ≤ 1 (genuine measure-theoretic model) + Born two-time correlation cos(2Δ) (from zenoU) +
-- quantum violation K₃(π/6) = 3/2 (Lüders bound) > 1. The record-layer/de-isolation denial of
-- non-invasive measurability is exactly why CSD is realist yet LG-violating.
/-- info: 'CSD.Empirical.QM.LeggettGarg.lg_macrorealist_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.LeggettGarg.lg_macrorealist_bound

/-- info: 'CSD.Empirical.QM.LeggettGarg.lgCorr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.LeggettGarg.lgCorr_eq

/-- info: 'CSD.Empirical.QM.LeggettGarg.lg_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.LeggettGarg.lg_violation

/-- info: 'CSD.Empirical.QM.LeggettGarg.lg_macrorealist_bound_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.LeggettGarg.lg_macrorealist_bound_violated

-- Quantum eraser (complementarity + which-path erasure, 2026-07-27): entangled path–marker Bell
-- state; joint P(a,c)=(1+ac cosφ)/4 fringe (erasure, marker-conditioned) vs flat system marginal
-- ∑_c P=1/2 (which-path info present) + bright/dark (visibility 1). Born-grounded (jointAmplitude).
/-- info: 'CSD.Empirical.QM.QuantumEraser.eraser_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.QuantumEraser.eraser_joint

/-- info: 'CSD.Empirical.QM.QuantumEraser.eraser_no_interference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.QuantumEraser.eraser_no_interference

/-- info: 'CSD.Empirical.QM.QuantumEraser.eraser_fringe_dark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.QuantumEraser.eraser_fringe_dark

-- Elitzur–Vaidman bomb tester (interaction-free measurement, 2026-07-27): balanced MZ (H·H=I) →
-- dark port 0 with no bomb (full interference); live bomb (which-path collapse) → dark port 1/4;
-- interaction_free (0 < 1/4): a dark click certifies the bomb without the photon hitting it.
/-- info: 'CSD.Empirical.QM.ElitzurVaidman.bomb_absent_dark_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.ElitzurVaidman.bomb_absent_dark_zero

/-- info: 'CSD.Empirical.QM.ElitzurVaidman.bomb_present_dark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.ElitzurVaidman.bomb_present_dark

/-- info: 'CSD.Empirical.QM.ElitzurVaidman.interaction_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.ElitzurVaidman.interaction_free

-- KCBS pentagon (state-dependent contextuality, noncontextual bound, 2026-07-27): K₅=∑⟨Πᵢ⟩≤2 over a
-- genuine measure-theoretic C₅ model (5 {0,1} observables, cyclic exclusivity) via the pentagon
-- independence-number pointwise bound + integral_mono. (QM √5 violation = separate pentagon-trig build.)
/-- info: 'CSD.Empirical.QM.KCBS.kcbs_noncontextual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.KCBS.kcbs_noncontextual_bound

-- KCBS QM √5 violation (pentagon on ℝ³, 2026-07-27): 5 unit vectors (kv_orth: consecutive
-- orthogonal, exclusivity) + apex; kcbs_qm_value (∑⟨ψ|Πᵢ|ψ⟩ = 5·(1/√5) = √5), kcbs_quantum_violation
-- (2 < √5). QM exceeds the noncontextual bound 2 → violates KCBS noncontextuality.
/-- info: 'CSD.Empirical.QM.KCBS.kcbs_qm_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.KCBS.kcbs_qm_value

/-- info: 'CSD.Empirical.QM.KCBS.kcbs_quantum_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.KCBS.kcbs_quantum_violation

/-- info: 'CSD.Empirical.QM.KCBS.kv_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.KCBS.kv_orth

-- Hong-Ou-Mandel (two-photon interference, 2026-07-27). Two identical bosons entering opposite
-- ports of a 50:50 beamsplitter (the corpus's own qmH) are NEVER found in different output ports:
-- hom_coincidence_zero (the DIP, = 0) / hom_bunching_one (= 1, they always leave together). The
-- whole effect is one matrix identity -- bsTwo_bosonIn, that H·σx·H is DIAGONAL, so the two
-- exchange paths cancel. The point is that this is EXCHANGE SYMMETRY, not optics: with the SAME
-- beamsplitter and the SAME input ports, distinct_coincidence_half gives 1/2 for distinguishable
-- particles (the classical baseline the dip drops below) and fermion_coincidence_one gives 1 --
-- Pauli anti-bunching, the exact opposite. hom_exchange_trichotomy is the 0 < 1/2 < 1 capstone;
-- inputs_normalised confirms all three inputs are unit vectors, so the comparison is honest.
-- Two-particle sector of two modes only -- no Fock space, no creation operators (CV/ApproxCCR
-- shows a finite model cannot carry the CCR exactly); HOM's content lives in the two-photon
-- amplitude, so this is the full effect, not a truncation of it.
/-- info: 'CSD.Empirical.HOM.bsTwo_bosonIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.bsTwo_bosonIn

/-- info: 'CSD.Empirical.HOM.hom_coincidence_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.hom_coincidence_zero

/-- info: 'CSD.Empirical.HOM.hom_bunching_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.hom_bunching_one

/-- info: 'CSD.Empirical.HOM.distinct_coincidence_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.distinct_coincidence_half

/-- info: 'CSD.Empirical.HOM.fermion_coincidence_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.fermion_coincidence_one

/-- info: 'CSD.Empirical.HOM.hom_dip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.hom_dip

/-- info: 'CSD.Empirical.HOM.hom_exchange_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.hom_exchange_trichotomy

/-- info: 'CSD.Empirical.HOM.inputs_normalised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.HOM.inputs_normalised

-- Context-fixed A7 at general N: the SUPPORT REDUCTION (2026-07-28, SigmaLayer/ContextFixedA7).
-- Step one of the general-N A7 no-go, and honest about being step one. Paper C A7 wants regions
-- Omega_i(M) fixed by the APPARATUS ALONE plus a preparation law; U(N)-covariance collapses the
-- density to g(|<psi|phi>|^2) for a SINGLE nonneg g. N=2 works (LF4/QubitBorn qubitBorn, g(s) =
-- 4(2s-1)+); N>=3 is OPEN IN BOTH DIRECTIONS (the earlier "provably dead" verdict rested on
-- numerics + an informal argument and was retracted 2026-07-28, specs/BACKLOG.md).
-- The reduction: evaluate A7 at the n BASIS-VECTOR preparations psi = e_j, where the Born weights
-- are delta_ij. For i != j the requirement makes a NONNEGATIVE integrand integrate to ZERO over
-- Omega_i, forcing it to vanish a.e. there (ae_eq_zero_of_setIntegral_eq_zero -- nonnegativity is
-- doing all the work, which is exactly what a SIGNED density would escape). Hence each support
-- sits in its own region (overlapSupport_ae_subset), the n supports are pairwise a.e. disjoint
-- (overlapSupports_ae_disjoint), and their measures sum to <= 1
-- (sum_measure_overlapSupport_le_one) -- so by symmetry each is <= 1/n while still carrying total
-- integral 1: a base-only density MUST SPIKE. That is what the N=2 solution, supported exactly on
-- (1/2, 1], is doing.
-- Stated over an ABSTRACT probability space on purpose: no projective geometry is needed, so the
-- reduction also survives a move to a fibred Sigma. Intended instantiation X := CPN n,
-- mu := fubiniStudyMeasure, s j := momentMap . j (momentMap_mk_eq_inner_sq).
-- NOT THE NO-GO. It constrains g; it does not refute it. Untouched: the generic-psi requirement
-- (everything here comes from the n basis-vector preps), and the harmonic argument (g(|<psi|phi>|^2)
-- integrated over a fixed region has components of every degree (k,k) while the target is pure
-- (1,1)) -- which needs harmonic analysis on CP^{n-1} that Mathlib does not have.
/-- info: 'CSD.SigmaLayer.ae_eq_zero_of_setIntegral_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.ae_eq_zero_of_setIntegral_eq_zero

/-- info: 'CSD.SigmaLayer.overlapSupport_ae_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.overlapSupport_ae_subset

/-- info: 'CSD.SigmaLayer.overlapSupports_ae_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.overlapSupports_ae_disjoint

-- STEP TWO (2026-07-28): THE CAP. The supports are A_i = {phi | s_i(phi) in S_g}, and step one
-- made them pairwise a.e. disjoint. If S_g contained a positive-measure set T of overlap values
-- BELOW 1/2, two coordinates could both land in T -- they would sum to < 1, so nothing forbids it
-- -- and at N >= 3 a third coordinate absorbs the remainder, so such states occur with POSITIVE
-- measure. Any of them lies in A_j AND A_k, contradicting disjointness. Hence
-- cap_of_joint_nondegenerate: g vanishes a.e. below 1/2. SHARP AND ATTAINED -- the N=2 solution
-- 4(2s-1)+ is supported exactly on (1/2, 1].
-- ★ WHY THE QUBIT ESCAPES, made precise: joint_degenerate_of_sum_eq_one. At N=2 the two Born
-- weights exhaust the state, s_j + s_k = 1, so they can NEVER both be below 1/2 -- the set is
-- literally EMPTY and the abundance hypothesis fails identically. That degeneracy IS the qubit's
-- escape route, and it closes at N >= 3 where the coordinates stop being functionally dependent.
-- base_only_density_confined assembles both halves: the density lives on measure <= 1/n AND only
-- where the overlap exceeds 1/2, while still integrating to 1.
-- The state-abundance input (hjoint) is an explicit HYPOTHESIS, not derived: deriving it is the
-- Dirichlet pushforward of mu_FS, real work and orthogonal to the argument. Stating it that way is
-- what makes the N=2 contrast visible.
/-- info: 'CSD.SigmaLayer.cap_of_joint_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.cap_of_joint_nondegenerate

/-- info: 'CSD.SigmaLayer.joint_degenerate_of_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.joint_degenerate_of_sum_eq_one

/-- info: 'CSD.SigmaLayer.base_only_density_confined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.base_only_density_confined

/-- info: 'CSD.SigmaLayer.sum_measure_overlapSupport_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.sum_measure_overlapSupport_le_one

-- BALANCED-STATE ABUNDANCE, DISCHARGED FOR mu_FS (2026-07-29, ContextFixedA7FS.lean).
-- fs_balanced_abundance: for every c above the forced minimum 1/(M+1), the projective points whose
-- moment coordinates are ALL <= c form a non-null set. This is the `hbalanced` hypothesis of
-- vanishes_below_of_balanced, so step five now has one of its two inputs supplied for mu_FS.
-- Proof: fs_volume_eq_dirichlet_inter reduces it to Lebesgue positivity, and a box about the
-- simplex barycentre witnesses it -- centre b = 1/(M+1), half-width d = min(b, c-b)/(M+1), the two
-- constraints being M*d < b (box stays inside sum t < 1) and M*d < c - b (the dropped coordinate
-- 1 - sum t stays below c).
-- ⚠️ LESSON: an earlier attempt on the same lemma FAILED across four iterations because b and d
-- were introduced with `set`, which makes them opaque local definitions that linarith/nlinarith
-- cannot see through. The fix was to SPLIT GEOMETRY FROM ARITHMETIC: box_in_simplex takes b and d
-- as ABSTRACT reals constrained by linear relations plus the single identity M*b = 1 - b, so every
-- step inside it is linear; the concrete choice is then made once, outside.
-- ⚠️ SCOPE: this does NOT make the (n-1)/n bound unconditional. Step four's OTHER input -- hdense,
-- the tilt fact that unit psi in the sphere of e_i-perp sweep overlaps across [0, 1 - s_i(phi)] --
-- is still a hypothesis and has not been attempted. And even with both discharged, the result is a
-- NECESSARY CONDITION on g, not a proof that A7 fails at N >= 3.
/-- info: 'CSD.SigmaLayer.volume_balanced_inter_openSimplexFree_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.volume_balanced_inter_openSimplexFree_pos

/-- info: 'CSD.SigmaLayer.fs_balanced_abundance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.fs_balanced_abundance

-- THE RE-PLUMBING (2026-07-29, SigmaLayer/CircleRecord.lean): the RECORD LAYER on the compact fibre.
-- CircleFibre.lean moved the Born PARTITION to AddCircle 1; this moves the rest with it -- the P5
-- record semantics, isolation-as-conditioning, measurement-as-(context + unknown microstate), the
-- Born probabilities, and a.e. totality of the readout.
-- ★ The RecordSignature is reused VERBATIM (fibreSignature: contexts are nonneg rate vectors,
-- outcomes are Fin n) because it never mentioned the fibre at all -- so swapping R for the circle
-- touches only the SEMANTICS, the assignment of ontic events. That is why nothing physical changes.
-- circleRecordSemantics (P5 on CompactSpace CircleFibre: events measurable + mutually exclusive);
-- compatibleSet_circle_single (P6 -- isolation = conditioning on the arc); circleOutcome_eq_record
-- (the ontic selection IS the record); circleBornMeasurement_prob (= ||psi i||^2, the SAME weight
-- the R fibre gave); circleBornMeasurement_ae_total.
-- ★ NOTE THE IMPROVEMENT in ae_total: on R the statement had to be RESTRICTED to [0,1) by hand,
-- because Lebesgue measure on the line is infinite. On the circle it is a statement about the WHOLE
-- space, because the whole space has measure one. That is the compactness paying for itself.
-- ⚠️ SCOPE unchanged: compactness + Haar probability measure YES; A1 in full NO (no Kahler structure
-- on the fibre; dw=0 needs manifold exterior calculus Mathlib lacks -- permanently scoped, see
-- reconstruction-status.md 2a). Measure exhibited as Haar, not SHOWN Liouville. And the general-N A7
-- question is PARKED, not settled (specs/sigma-fibre-contextuality.md).
/-- info: 'CSD.RecordLayer.circleRecordSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleRecordSemantics

/-- info: 'CSD.RecordLayer.compatibleSet_circle_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.compatibleSet_circle_single

/-- info: 'CSD.RecordLayer.circleOutcome_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleOutcome_eq_record

/-- info: 'CSD.RecordLayer.circleBornMeasurement_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleBornMeasurement_prob

/-- info: 'CSD.RecordLayer.circleBornMeasurement_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleBornMeasurement_ae_total

-- THE FIBRE SWAP (2026-07-29, SigmaLayer/CircleFibre.lean) -- the Born partition on a COMPACT fibre.
-- ⚠️ THE DIAGNOSIS THIS FIXES: the corpus had TWO record-layer constructions and COMPACTNESS AND
-- FIBRE-ACTIVITY SAT IN DIFFERENT ONES. KSigmaRecord puts a P5 RecordSemantics on the COMPACT
-- KSigma = CPN x T^2, but its events are pi^-1(bornRegion psi i) -- pulled back from the BASE, so
-- the torus fibre is INERT and it inherits the preparation-indexed base regions. FibredSigma has an
-- ACTIVE fibre (it carries the CDF Born cells) but that fibre is R -- NOT COMPACT, so it cannot be a
-- Paper C A1 ontic surface. Neither had both, and since the A7 work concluded contextuality must
-- live in the FIBRE, active-fibre-on-compact-Sigma is exactly what was needed.
-- circleFibre_volume_univ + the CompactSpace instance: the fibre is AddCircle 1 -- the same factor
-- KTorus is built from -- compact, with Haar a genuine PROBABILITY measure (what restricted Lebesgue
-- on R only had by fiat). circleCell is defined as a PREIMAGE under the canonical representative
-- map, not as an image of cdfCell, so measurability is immediate (measurableSet_circleCell).
-- volume_circleCell: the cell carries EXACTLY the Born weight r_i, via Mathlib's
-- AddCircle.measurePreserving_equivIoc -- so moving to a compact fibre changes NOTHING about the
-- outcome probabilities. volume_circleBornCell: fed the Born rates, the measure is ||psi i||^2.
-- circleCell_pairwiseDisjoint: distinct outcomes stay mutually exclusive.
-- ⚠️ SCOPE: this supplies the FIBRE half. It does NOT by itself make the fibred Sigma an A1 ontic
-- surface, and the measure is exhibited as Haar, not SHOWN to be Liouville.
-- FibreRecord/Measurement/RecordLayerClosure still run on the R fibre and would need re-plumbing
-- onto this one -- NOT done (CircleRecord.lean is a PARALLEL counterpart, not a migration).
-- ⚠️ CORRECTED 2026-07-30: this block previously said the missing Kahler structure needed "the
-- manifold exterior calculus Mathlib lacks; see reconstruction-status.md 2a scoping decision".
-- That was a MISCLASSIFICATION. CP^{n-1} x AddCircle 1 has real dimension 2n-1 -- ODD -- and no
-- odd-dimensional manifold admits a symplectic, hence Kahler, structure. It is a PARITY fact, not
-- a tooling gap, and no Mathlib API repairs it. See TorusFibre.lean, which moves the partition to
-- the even-dimensional KTorus.
/-- info: 'CSD.RecordLayer.circleFibre_volume_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleFibre_volume_univ

/-- info: 'CSD.RecordLayer.measurableSet_circleCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurableSet_circleCell

/-- info: 'CSD.RecordLayer.circleCell_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.circleCell_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.volume_circleCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.volume_circleCell

/-- info: 'CSD.RecordLayer.volume_circleBornCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.volume_circleBornCell

-- THE PARITY FIX (2026-07-30, SigmaLayer/TorusFibre.lean) -- the Born partition on KTorus.
-- ⚠️ WHAT THIS FIXES, and it is NOT what the fibre-swap block above first said. CircleFibre closed
-- the COMPACTNESS objection but left a second one that is NOT a tooling gap: CP^{n-1} has real
-- dimension 2n-2, so CP^{n-1} x AddCircle 1 has real dimension 2n-1 -- ODD. A symplectic form needs
-- w^k as a volume form, so no odd-dimensional manifold carries one, hence none carries a Kahler
-- structure. A SINGLE CIRCLE CAN THEREFORE NEVER BE THE FIBRE OF A PAPER C A1 SURFACE, however much
-- differential-geometry API Mathlib grows. The same applies retroactively to FibredSigma's
-- CP^{n-1} x R, also 2n-1.
-- THE FIX WAS ALREADY IN THE CORPUS: LF4/KahlerInstance.lean's KTorus = AddCircle 1 x AddCircle 1,
-- with KSigma N = CPN N x KTorus of real dimension 2n -- EVEN, compact, a product of Kahler
-- manifolds. This file puts the cells on the FIRST torus coordinate, leaving the second free as its
-- symplectic partner (mem_torusCell_iff states that freedom as a theorem, rather than leaving it to
-- the prose).
-- volume_torusCell: the cell carries EXACTLY the Born weight r_i -- the free coordinate contributes
-- a factor of 1 because T^2's Haar measure is a probability measure -- so moving to the
-- even-dimensional arena changes NOTHING about the outcome probabilities, just as compactifying did
-- not. volume_torusBornCell: fed the Born rates, the measure is ||psi i||^2.
-- torusCell_pairwiseDisjoint: exclusivity, inherited coordinatewise. torusCell_ae_total /
-- torusBornCell_ae_total: the cells cover T^2 up to a null set.
-- ⚠️ SCOPE: this REMOVES AN OBSTRUCTION to A1; it does not ESTABLISH A1. KSigma is not proved Kahler
-- here, and the fibre measure is exhibited as Haar, not shown to be Liouville. The partition is also
-- still KINEMATIC and still PREPARATION-INDEXED (the consumer feeds it bornRate psi). The successor
-- is the global context-fixed basin B_i(M) with the moment map evaluated at the ONTIC POINT, which
-- is NOT in this file and needs measurability of momentMap -- a lemma the corpus does not have.
/-- info: 'CSD.RecordLayer.mem_torusCell_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.mem_torusCell_iff

/-- info: 'CSD.RecordLayer.measurableSet_torusCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurableSet_torusCell

/-- info: 'CSD.RecordLayer.volume_torusCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.volume_torusCell

/-- info: 'CSD.RecordLayer.torusCell_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.torusCell_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.volume_torusBornCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.volume_torusBornCell

/-- info: 'CSD.RecordLayer.torusBornCell_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.torusBornCell_ae_total

-- MOMENT-MAP REGULARITY (2026-07-30, LF4/MomentMap.lean) -- the prerequisite for the basin.
-- momentMap is DEFINED through p.rep, a Classical.choice representative, so it cannot be attacked
-- directly: Projectivization.rep is not continuous out of P, and no unfolding makes it so. The route
-- is the QUOTIENT -- the coordinate ratio is continuous on the nonzero subtype and scale-invariant
-- (momentRatio_smul), and mk' is a quotient map (Projectivization.isQuotientMap_mk'), so the
-- descended function is continuous. Measurability is then IMMEDIATE, because P K V carries the BOREL
-- sigma-algebra of that same topology (Projectivization.instBorelSpace).
-- ⚠️ ESTIMATE CORRECTION: this was logged as effort M on the assumption the infrastructure was
-- missing. It is S -- Projectivization/Topology.lean and Projectivization/MeasureSpace.lean already
-- staged continuous_iff_continuous_comp_mk' and the Borel instance. The row was wrong, not the work.
/-- info: 'CSD.LF4.continuous_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.continuous_momentMap

/-- info: 'CSD.LF4.measurable_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.measurable_momentMap

-- ★★ THE CONTEXT-FIXED GLOBAL BASIN (2026-07-30, SigmaLayer/GlobalBasin.lean) -- Paper C A7, fibred.
-- THE DEFECT THIS CLOSES: the corpus's record-layer partition is cdfCell (bornRate psi) -- built from
-- the PREPARATION -- so it was never the Omega_i(M) Paper C A7 asks for. QubitBorn does it at N = 2;
-- the general-N BASE-ONLY question is PARKED (ContextFixedA7*, sigma-fibre-contextuality.md).
-- THE CONSTRUCTION (due to an external review of 29c6afd): B_i = {(p, t1, t2) : t1 in circleCell
-- (rate p) i}, with the rate vector read off AT THE ONTIC POINT p. NO psi APPEARS IN THE DEFINITION,
-- so the basin is a function of the apparatus context alone. ContextField bundles what a context
-- actually contributes: a measurable simplex-valued rate FIELD on the base.
-- measurableSet_globalBasin: cut out by two inequalities between measurable real functions
-- (measurable_rep, the rate field, its partial sums) -- this is the step measurable_momentMap unblocks.
-- globalBasin_prob: conditioning the epistemic state on p returns rate p i, via Measure.prod_apply +
-- lintegral_dirac and the TorusFibre slice (preimage_globalBasin). globalBasin_born: at preparation
-- psi the probability is EXACTLY ||<e_i, psi>||^2 -- the Born rule from a partition that never
-- mentions psi. globalBasin_pairwiseDisjoint, globalBasin_ae_total.
-- ★ NOT CIRCULAR: bornRate_eq_momentMap already has the rates FORCED by the Kahler structure and the
-- T^n action, not carved to a target. ★ DOES NOT COLLIDE with the parked N>=3 chain, which constrains
-- BASE-ONLY densities; this partition is genuinely FIBRED, exactly where the fibre-contextuality
-- finding said it must live.
-- ⚠️ SCOPE. (1) dirac p (x) Haar is the EPISTEMIC measure, NOT the Liouville measure. Conditioning on
-- a preparation conditions on a mu_FS-NULL set, so the Dirac product is taken as a DEFINITION rather
-- than obtained by disintegration -- a modelling choice, not a theorem. kMuL = mu_FS (x) vol remains
-- the Liouville measure. (2) KINEMATIC: no H_int(M) generating these basins is constructed; the Paper
-- D obligation is untouched. (3) This does NOT close general-N A7 outright -- it closes the
-- PREPARATION-INDEXING defect. Whether Paper C intends the regions to be BASE-ONLY (in which case the
-- parked chain still governs) is a question about the axiom, not about this file. (4) KSigma is still
-- not proved Kahler and the fibre measure is still Haar, not shown Liouville.
/-- info: 'CSD.RecordLayer.measurableSet_globalBasin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurableSet_globalBasin

/-- info: 'CSD.RecordLayer.globalBasin_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalBasin_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.globalBasin_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalBasin_prob

/-- info: 'CSD.RecordLayer.globalBasin_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalBasin_ae_total

/-- info: 'CSD.RecordLayer.globalBasin_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalBasin_born

-- ★★ THE RECORD-LAYER CAPSTONE, MIGRATED (2026-07-31, SigmaLayer/GlobalRecordClosure.lean).
-- RecordLayerClosure certifies the record layer on the fibre Sigma = R with fibreTypicality, for the
-- context bornContext psi -- BUILT FROM THE PREPARATION. This bundle certifies THE SAME FIVE FACTS on
-- the corpus's actual compact sector KSigma = CPN x T^2, for a ContextField -- built from the
-- APPARATUS ALONE. What moved: the arena (R, odd-dimensional, -> KSigma, even), the context type
-- (bornContext psi -> ContextField), the measure (fibreTypicality -> epistemicMeasure p).
-- ★ THE RECORD EVENT IS NOW A FUNCTION OF (context, outcome, time) AND NOTHING ELSE. That is visible
-- in the TYPE of globalRecordSemantics and needs no theorem: the SAME set globalBasin c i serves
-- every preparation, and only the epistemic measure moves. Under fibreRecordSemantics the event was
-- cdfCell (bornRate psi), so it moved with psi. That is the defect A7 objected to.
-- ★ globalOutcome is LITERALLY circleOutcome read at the point's own base, so the ontic selection
-- needs no new machinery -- globalOutcome_eq_some_iff is circleOutcome_eq_some_iff plus unfolding.
-- ★ ae_total STRENGTHENS: on R it had to be stated relative to Ico 0 1 because Lebesgue on the line
-- is infinite; here it is about the WHOLE SPACE, which has measure one.
-- THAT THE FIVE FIELDS ARE OTHERWISE IDENTICAL is the evidence that neither defect was ever
-- load-bearing for the record layer's CONTENT.
-- ⚠️ SCOPE, unchanged from GlobalBasin and repeated because this is the capstone. (1) epistemicMeasure
-- is the EPISTEMIC measure, a definition not a disintegration, and NOT the Liouville measure.
-- (2) KINEMATIC -- no H_int(M); the Paper D obligation is untouched and a certified readout is not a
-- dynamical account of measurement. (3) Closes the PREPARATION-INDEXING defect, not general-N A7
-- outright. (4) RecordLayerClosure is SUPERSEDED, NOT DELETED -- still true, still consumed -- and
-- FiniteQMClosure still carries the older vnPointerOutcome readout; swapping THAT is a separate
-- migration on the productDynamics engine and is NOT done here.
/-- info: 'CSD.RecordLayer.globalOutcome_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalOutcome_eq_some_iff

/-- info: 'CSD.RecordLayer.compatibleSet_global_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.compatibleSet_global_single

/-- info: 'CSD.RecordLayer.globalRecordClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalRecordClosure

/-- info: 'CSD.RecordLayer.globalRecordClosure_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.globalRecordClosure_born

-- CONSTRAINTS ON THE UNBUILT DYNAMICAL LAYER (2026-08-01, SigmaLayer/MeasurementConstraints.lean).
-- ⚠️ THE DIAGNOSIS THAT FORCED THIS (external review, and it is SHARPER than the "still kinematic"
-- caveat the GlobalBasin block carries): globalBasin_ae_total shows the basins cover Sigma up to a
-- null set, so A.E. EVERY POINT ALREADY CARRIES A RECORD and there is no apparatus-ready state of
-- positive measure. A flow cannot CREATE a record in such a space. So "add dynamics to
-- GlobalRecordClosure" is not merely incomplete, it is STRUCTURALLY IMPOSSIBLE -- the repair has to
-- split the hidden SELECTOR from a pointer REGISTER with its own ready region.
-- This file builds none of that. It derives NECESSARY CONDITIONS on any such witness from measure
-- preservation and continuity alone, BEFORE a Hamiltonian exists -- the same cheap-failure check the
-- CP^{n-1} x S^1 parity argument would have been.
-- pointer_region_measure_ge: mu_sel(S) * mu_R(R_0) <= mu_R(B). ⚠️ THE MEASURE CHECK COMES BACK
-- NEGATIVE -- it does NOT obstruct. Granting the (unformalised) evaluation mu_sel(S_i) = 1/n, it
-- reads mu_R(B_i) >= mu_R(R_0)/n, satisfiable with room. That is a GREEN LIGHT for attempting the
-- concrete H_int, NOT evidence that a witness exists. ready_region_measure_le: the summed form,
-- recorded explicitly AS WEAK rather than dressed up.
-- ★ no_everywhere_correlation IS THE ONE WITH TEETH. A continuous Phi maps the preconnected
-- S x R_0 to a preconnected image, which cannot meet two DISJOINT OPEN pointer regions. So an
-- EVERYWHERE correlation is impossible for n >= 2. THEREFORE THE "a.e." IN THE CORRELATION THEOREM
-- IS MATHEMATICALLY NECESSARY, NOT A CONVENIENCE: the exceptional set must be NON-EMPTY, it contains
-- the seams between selector sectors, and its image threads the gaps between pointer regions.
-- Consequences for the implementer: any candidate H_int advertised as giving an exact/everywhere
-- correlation is wrong on these grounds alone; and a witness that leaves the seam unspecified has
-- not addressed the hardest part of its own statement.
/-- info: 'CSD.RecordLayer.pointer_region_measure_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pointer_region_measure_ge

/-- info: 'CSD.RecordLayer.ready_region_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.ready_region_measure_le

/-- info: 'CSD.RecordLayer.no_everywhere_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.no_everywhere_correlation

-- THE DYNAMICAL MEASUREMENT INTERFACE (2026-08-01, SigmaLayer/MeasurementProtocol.lean) -- items 1-2.
-- Supplies what GlobalBasin structurally could not: a POINTER REGISTER whose ready region is
-- disjoint from every outcome region, plus a TWO-TIME propagator Phi_{s->t} (not a one-parameter
-- group -- a measurement interaction is switched on and off, and a time-dependent H_int(M,t) does
-- not generate a group).
-- ★ THE DESIGN RULE. The plan warns that a structure with fields like basin_has_born_measure or
-- record_persists "would merely rename the assumptions". Taken literally here: MeasurementProtocol
-- carries ONLY KINEMATICS -- propagator laws, regions, measurability, disjointness, every one a
-- CHECKABLE property of the data. THE CORRELATION IS NOT A FIELD. It is CorrelatesOn, a HYPOTHESIS
-- of the theorems that need it (CONVENTIONS 8.3 _of_ pattern), so discharging it is the visible act
-- of REMOVING a hypothesis. The corpus already has one field-shaped assumption of the forbidden kind
-- (DeIsolationInteraction.basin_rate) and this file deliberately does not add a second.
-- readout_ready_eq_none: BEFORE THE INTERACTION THERE IS NO RECORD -- the non-triviality condition
-- GlobalBasin could not state, and what stops a pre-existing label being sold as a created record.
-- outcomeSector i = Phi_{0->T}^{-1}(B_i): the INITIAL states DESTINED for record i, as against the
-- pointer region where a record is DISPLAYED. That is the TN6 two-level distinction, and conflating
-- the two is what makes a kinematic partition look dynamical.
-- readout_evolve_outcomeSector bridges the levels; outcomeSector_pairwiseDisjoint inherits
-- exclusivity through the preimage.
-- ★ measure_outcomeSector_eq_of_correlates: THE BORN WEIGHT, DERIVED. Given the correlation, the
-- outcome sector's measure EQUALS the selector sector's -- so the dynamic probability is not a new
-- postulate, it is the existing context-fixed selector weight transported by the interaction.
-- Composed with globalBasin_born it yields ||<e_i,psi>||^2.
-- ⚠️ NO INTERACTION HAMILTONIAN. Nothing here constructs a Phi satisfying CorrelatesOn; that is the
-- open Paper D obligation. Every theorem is pure kinematics or explicitly conditional. This file is
-- SCAFFOLDING FOR THE STATEMENT of the problem, NOT progress on its solution.
-- ⚠️ And by no_everywhere_correlation above, the EVERYWHERE form of CorrelatesOn is UNSATISFIABLE at
-- K >= 2 on a connected ready set. A real witness establishes it only off a null set and must say
-- what happens on the seam.
/-- info: 'CSD.RecordLayer.MeasurementProtocol.readout_ready_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.readout_ready_eq_none

/-- info: 'CSD.RecordLayer.MeasurementProtocol.outcomeSector_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.outcomeSector_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.MeasurementProtocol.readout_evolve_outcomeSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.readout_evolve_outcomeSector

/-- info: 'CSD.RecordLayer.MeasurementProtocol.measure_outcomeSector_eq_of_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.measure_outcomeSector_eq_of_correlates

-- PERSISTENCE AND THE POST-MEASUREMENT ENSEMBLE (2026-08-01, SigmaLayer/RecordPersistence.lean) --
-- items 5-6.
-- ★ BOTH USE THE EVOLUTION, WHICH IS THE POINT. The plan is explicit that reusing the same set at
-- every time does not count as persistence. record_persists_on_interval is stated about
-- evolve startTime t for a RANGE of t and its proof runs through evolve_comp
-- (Phi_{0->t} = Phi_{T->t} . Phi_{0->T}), so it is a statement about the PROPAGATOR, not the
-- observation that a time-independent set is time-independent. Likewise postMeasure is a genuine
-- pushforward along the propagator, not a relabelling of the conditioned measure.
-- PointerInvariantOn: the post-readout invariance HYPOTHESIS -- again NOT a field, for the same
-- reason CorrelatesOn is not. It is an assumption ABOUT THE DYNAMICS; a witness must establish it,
-- by forward invariance of B_i or by a conserved pointer observable.
-- record_persists_on_interval: a state destined for i is in B_i at EVERY time of [T_M, T_M + tau_R].
-- readout_persists_on_interval: the readout-level form -- and therefore the POINTER-LEVEL
-- REPEATABILITY statement, a second look during the lifetime returns the recorded outcome.
-- ★ SELECTION vs DISTURBANCE, which the corpus previously could not distinguish:
-- measure_outcomeSector_eq_of_correlates says WHICH initial sector produced outcome i (selection);
-- postMeasure says WHERE THE SELECTED ENSEMBLE ENDS UP (disturbance).
-- postMeasure_supported_pointerRegion: the whole selected ensemble lands in B_i, probability one.
-- Almost definitional -- Phi^{-1}(B_i) IS Omega_i by construction -- and that is the RIGHT shape,
-- not a weakness: the content is the definitions lining up. Holds for ANY propagator, needing
-- neither CorrelatesOn nor PointerInvariantOn.
-- ⚠️ SCOPE. No interaction Hamiltonian: PointerInvariantOn is ASSUMED, not constructed, so nothing
-- here advances the open Paper D obligation. AND THE LUDERS BRIDGE IS NOT HERE -- item 6 also asks
-- that after the system-reduction map r_S this reproduce rho -> Pi_i rho Pi_i / Tr(rho Pi_i), which
-- needs a reduction map from Sigma_meas to the system density operator that the corpus does NOT have
-- for this arena. The measure-theoretic half is done; the bridge to LF5's Luders result is not, and
-- is not claimed. The finite window [T_M, T_M + tau_R] is deliberate -- on a compact phase space with
-- an invariant probability measure, indefinite stability raises recurrence questions finite-QM
-- closure does not need.
/-- info: 'CSD.RecordLayer.MeasurementProtocol.record_persists_on_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.record_persists_on_interval

/-- info: 'CSD.RecordLayer.MeasurementProtocol.readout_persists_on_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.readout_persists_on_interval

/-- info: 'CSD.RecordLayer.MeasurementProtocol.postMeasure_supported_pointerRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.MeasurementProtocol.postMeasure_supported_pointerRegion

-- ★★ THE CONCRETE MEASUREMENT WITNESS (2026-08-01, SigmaLayer/ShearWitness.lean) -- item 3, PARTLY.
-- An explicit propagator on Sigma_sel x T^2_R that takes a ready pointer into one displaying the
-- outcome the hidden selector had already fixed. It DISCHARGES BOTH standing hypotheses of the
-- interface -- CorrelatesOn AND PointerInvariantOn -- so neither is assumed.
-- THE PHYSICS: the von Neumann shear H_int(t) = g(t)(iota(x_sel)+1) delta p_R. Hamilton gives
-- qdot_R = g(t)(iota+1)delta, pdot_R = 0, and -- the point -- xdot_sel ~ grad(iota) = 0 A.E.,
-- because iota is LOCALLY CONSTANT off the seams between selector sectors. So the coupling moves the
-- pointer at an outcome-dependent rate and does NOT disturb the selector, except on the measure-zero
-- seam. ★ THAT IS EXACTLY WHERE no_everywhere_correlation SAID THE EXCEPTIONAL SET HAD TO LIVE --
-- the constraint predicted the singularity's location before the construction existed. Two
-- independent routes agreeing is the reason to think this is the right shape.
-- DESIGN, each choice forced: shifts of (i+1)delta not i*delta (else the outcome-0 region IS the
-- ready region and "no record" masquerades as a record); g SWITCHED OFF after T_M (which is why the
-- interface is a TWO-TIME propagator -- a group cannot express the switch-off, and it is what makes
-- shear_pointerInvariant PROVABLE); epsilon = delta/2 with delta = 1/(K+1) (arcs pairwise disjoint
-- in one turn, AND every shifted ready state stays below 1 so no wraparound occurs and rep is
-- additive -- rep_pshift_of_mem).
-- shear_correlates: CorrelatesOn DISCHARGED. shear_pointerInvariant: PointerInvariantOn DISCHARGED.
-- shear_readout_ready / shear_readout_after: the non-triviality pair -- NO record before, a unique
-- record after -- which rules out an identity flow or a pre-existing label sold as record creation.
-- ⚠️ SCOPE, and item 3 IS NOT CLOSED. (1) THE HAMILTONIAN GENERATION IS STATED, NOT FORMALISED: the
-- propagator is constructed explicitly and every required property proved OF it, but that it is the
-- time-T_M flow of that H_int is symplectic geometry and Mathlib has no manifold Hamiltonian-flow
-- API (the section 2a permanently-scoped row). The plan's "propagator PROVED TO ARISE FROM that
-- Hamiltonian" is therefore HALF done. Do not cite this as a formalised H_int. (2) MEASURE
-- PRESERVATION IS NOT PROVED -- and it matters, because it is what makes this a DYNAMICS rather than
-- an arbitrary relabelling, and every necessary condition in MeasurementConstraints assumes it.
-- First thing to close. (3) NOT connected to the Born weights: that needs the selector sectors to be
-- globalBasin's, which depends on (2). (4) A WITNESS, NOT A DERIVATION -- the coupling is ENGINEERED
-- to work. (5) iota is the outcome index, so "the apparatus is coupled to the answer" -- an
-- objection that applies verbatim to the textbook von Neumann coupling this is the ontic analogue of.
/-- info: 'CSD.RecordLayer.rep_pshift_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.rep_pshift_of_mem

/-- info: 'CSD.RecordLayer.shear_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_correlates

/-- info: 'CSD.RecordLayer.shear_pointerInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_pointerInvariant

/-- info: 'CSD.RecordLayer.shear_readout_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_readout_after

-- MEASURE PRESERVATION FOR THE SHEAR (2026-08-01) -- closing scope item (2) of the block above.
-- ⚠️ That block recorded measure preservation as NOT PROVED, and warned it MATTERED: it is what makes
-- the witness a DYNAMICS rather than an arbitrary relabelling of states, and EVERY necessary
-- condition in MeasurementConstraints assumes it. It is now proved, so that warning is discharged.
-- shear_measurePreserving: a SKEW PRODUCT -- the selector is held fixed and each fibre is translated
-- by a Haar-preserving shift (measurePreserving_pshift, from translation invariance of Haar on the
-- compact group T^2). The instance IsAddLeftInvariant for volume on KTorus had to be supplied by
-- hand: volume on a product IS the product measure, but the invariance instance does not fire
-- through the MeasureSpace instance.
-- CONSEQUENCE: the Born connection (scope item 6) is now UNBLOCKED -- what remains there is the
-- instantiation of the selector sectors as globalBasin's, not a missing ingredient.
-- ⚠️ STILL OPEN and unchanged: the Hamiltonian generation is stated, not formalised (no manifold
-- Hamiltonian-flow API in Mathlib), so item 3 remains only PARTLY closed.
/-- info: 'CSD.RecordLayer.measurePreserving_pshift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurePreserving_pshift

/-- info: 'CSD.RecordLayer.shear_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_measurePreserving

-- THE SHEAR DRIVEN BY THE CONTEXT-FIXED BASINS (2026-08-01, SigmaLayer/DynamicBorn.lean) -- item 4.
-- ShearWitness proves the correlation for an ABSTRACT measurable index. This supplies the index the
-- architecture intends -- the one read off globalBasin -- so the dynamical sectors carry BORN
-- WEIGHTS rather than arbitrary ones.
-- basinIndex: the outcome index of a point of Sigma_sel. Its fibre over i is globalBasin c i, except
-- over the DEFAULT index which also picks up the points in NO basin -- a null set by
-- globalBasin_ae_total. measure_basinIndex_fibre: that null set costs nothing, so every fibre has
-- exactly its basin's measure. (This is the one place the a.e.-totality that caused the original
-- problem is actually USEFUL: it is what makes the default index harmless.)
-- ★ shear_selector_born: at preparation psi the sector "hidden selector reads i AND apparatus ready"
-- has measure ||<e_i,psi>||^2. Composed with shear_correlates and
-- measure_outcomeSector_eq_of_correlates, the DYNAMICAL outcome weight IS the Born weight -- the
-- probability is TRANSPORTED BY THE INTERACTION, not posited for it.
-- ⚠️ SCOPE unchanged from ShearWitness: the propagator is explicit and every property proved OF it,
-- but the HAMILTONIAN GENERATION IS STATED, NOT FORMALISED. This closes the BORN half of item 4, not
-- item 3.
/-- info: 'CSD.RecordLayer.measurable_basinIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurable_basinIndex

/-- info: 'CSD.RecordLayer.measure_basinIndex_fibre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measure_basinIndex_fibre

/-- info: 'CSD.RecordLayer.shear_selector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_selector_born

-- GENERALISATION AND THE DYNAMICAL CAPSTONE (2026-08-01, OutcomeField + DynamicMeasurementClosure)
-- items 7-8.
-- ITEM 7. ContextField N ties the OUTCOME COUNT to the DIMENSION (rate : CPN N -> Fin N), which is
-- right for a NONDEGENERATE measurement and wrong for everything else. OutcomeField N K decouples
-- them. ★ TWO PLAN CONSTRAINTS FOLLOWED LITERALLY: (a) introduced ALONGSIDE ContextField, NOT
-- replacing its uses -- globalBasin and everything downstream are untouched, and
-- ContextField.toOutcomeField shows the generalisation is CONSERVATIVE; (b) an arbitrary
-- simplex-valued field is NOT treated as automatically physical -- OutcomeField is a
-- measurability-and-simplex condition and inhabiting it proves nothing about an apparatus.
-- The physical content is blockField: given a DEGENERACY MAP b : Fin N -> Fin K, the rate of outcome
-- i is the total moment-map weight of its block, the ontic form of <psi, Pi_i psi>. Every field
-- condition comes FREE from the moment map's, because it is a FINITE SUM OF MOMENT COORDINATES --
-- the same object, coarse-grained. blockField_id recovers momentContext, so the nondegenerate case
-- is recovered rather than replaced. ⚠️ globalBasin still consumes a ContextField, so an
-- OutcomeField cannot yet DRIVE the dynamical layer -- that bridge is deliberately not built.
-- ITEM 8. ADDITIVE, NOT DESTABILISING, exactly as the plan required: FiniteQMClosure is UNTOUCHED.
-- DynamicMeasurementClosure bundles the five dynamical facts: ready => no record; a record is
-- CREATED and is the outcome the selector fixed; outcomes exclusive; the record PERSISTS across the
-- operational window; the selector weights ARE the Born weights.
-- ★ NOTE WHAT IS ABSENT FROM ITS HYPOTHESES: CorrelatesOn and PointerInvariantOn DO NOT APPEAR,
-- because ShearWitness discharged them from an explicitly constructed propagator. This bundle rests
-- on a CONSTRUCTION, not on assumed dynamics -- the difference between it and every earlier
-- record-layer bundle in the corpus.
-- ⚠️ The post-measurement/Luders field is DELIBERATELY NOT bundled: postMeasure_supported_pointerRegion
-- exists but the Luders bridge needs a system-reduction map the corpus lacks for this arena, so
-- including it would overstate.
-- CsdFiniteQMClosure combines operational + dynamic. ⚠️ IT ASSERTS BOTH BUNDLES HOLD; IT DOES NOT
-- ASSERT THEY ARE ABOUT THE SAME ARENA. The operational closure lives on productDynamics over
-- CP^M x T^2 for a composite indexed by Fin Nsub x Fin Nsub ~ Fin (M+1); the dynamical one on
-- Sigma_sel x T^2_R in dimension Nsys. The parameter lists are DISJOINT, and that is the honest
-- state of the corpus, not an encoding artefact. Unifying the arenas is the ENGINE MIGRATION and is
-- NOT done. Read it as "both hold", not "one theory covers both".
-- ⚠️ And item 3's residue is unchanged: the Hamiltonian generation is STATED, NOT FORMALISED. A
-- capstone cannot launder that.
/-- info: 'CSD.RecordLayer.blockField_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.blockField_id

/-- info: 'CSD.RecordLayer.dynamicMeasurementClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.dynamicMeasurementClosure

/-- info: 'CSD.RecordLayer.csdFiniteQMClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.csdFiniteQMClosure

-- THE TWO REMAINING BRIDGES (2026-08-01).
-- BRIDGE A -- OutcomeField -> basins (SigmaLayer/OutcomeBasin.lean). OutcomeField decoupled the
-- outcome count from the dimension but globalBasin still consumed a ContextField, so a K-outcome
-- field could not drive the record layer. outcomeBasin closes that: same construction, Fin K in
-- place of Fin N, with measurability, exclusivity, outcomeBasin_prob and a.e. totality re-proved.
-- ★ outcomeBasin_toOutcomeField: for a ContextField the generalised basin IS globalBasin,
-- DEFINITIONALLY -- the generalisation adds cases without changing any existing one. So DEGENERATE
-- PROJECTIVE MEASUREMENTS now reach the basins.
-- BRIDGE B -- THE LUDERS CONNECTION, AND IT IS A NEGATIVE RESULT.
-- ⚠️ shear_base_marginal_unchanged: Prod.fst . evolve = Prod.fst, so the base marginal of the
-- POST-measurement ensemble is the base marginal of the SELECTED ensemble. NOTHING ABOUT THE SYSTEM
-- HAS MOVED. The shear therefore gives REPEATABILITY (re-reading the same observable returns the
-- same outcome) but does NOT implement the LUDERS UPDATE: after outcome i the system is still at
-- [psi], not at [e_i], so a subsequent INCOMPATIBLE measurement would see the original preparation
-- -- which is not what QM predicts.
-- ★ THE TENSION IS STRUCTURAL, NOT AN OVERSIGHT. The property that makes this witness work --
-- xdot_sel ~ grad(iota) = 0, NO BACK-REACTION on the selector -- is EXACTLY the property that
-- prevents collapse. A witness reproducing Luders must DISTURB the selector, and then the clean
-- correlation argument has to be redone. So item 6's Luders half is not merely unbuilt here: THIS
-- WITNESS CANNOT SUPPLY IT, and a different coupling is required. Recorded as a theorem rather than
-- left as an absence, so the limitation is machine-checked rather than asserted.
/-- info: 'CSD.RecordLayer.outcomeBasin_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.outcomeBasin_prob

/-- info: 'CSD.RecordLayer.outcomeBasin_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.outcomeBasin_ae_total

/-- info: 'CSD.RecordLayer.shear_base_marginal_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_base_marginal_unchanged

-- ★★ THE CALIBRATED-SWAP WITNESS AND THE LUDERS THEOREM (2026-08-01/02, SigmaLayer/SwapWitness.lean
-- + SwapLuders.lean + MeasurementConstraints additions + Mathlib/MeasureTheory/PiecewisePreserving).
-- shear_base_marginal_unchanged proved the shear CANNOT collapse: no back-reaction on the selector
-- is exactly what prevents it. The design (Fable review, 2026-08-01) starts from TWO NO-GOS proved
-- FIRST, in MeasurementConstraints:
--   no_exact_collapse        a measure-preserving map cannot send a positive-measure set of states
--                            into a NULL target (the basis vertices). So pointwise collapse across
--                            preparations is IMPOSSIBLE, and collapse must be RELOCATION of a null
--                            epistemic slice, never contraction.
--   collapse_accuracy_bound  approximate collapse to eps-balls forces mu_R(R_0) <= N mu_FS(ball) --
--                            COLLAPSE ACCURACY IS PAID IN READY-STATE IMPROBABILITY (Landauer as a
--                            measure inequality). Retroactively FORCES the Dirac-calibration
--                            convention rather than excusing it.
-- THE CONSTRUCTION: enlarge the arena with an ANCILLA BANK, SwapArena = (Xsel x T^2_R) x (Fin K ->
-- Xsel) -- K reference cells, one per outcome, each a full copy of the selector space. Propagator =
-- record-triggered swap AFTER the shear: when the pointer sits in arc j, exchange the system's
-- selector coordinate with bank slot j (swapG, an INVOLUTION).
-- ★ THE RECORD-TRIGGER IS FORCED: the pieces {register in arc j} are invariant under the slot-j swap
-- BECAUSE the swap never touches the register -- which is what makes swapG measure-preserving via
-- measurePreserving_of_partition. Triggering on the SELECTOR index would move the coordinate the
-- pieces are defined by, and the bookkeeping fails. The right causal story and the only working
-- measure theory COINCIDE.
-- ★ THE CROSSING PROPAGATOR IS SYMMETRIC -- a CORRECTION to the reviewed design, which fired the
-- swap on forward readout-crossings only. evolve_comp is quantified over ALL time triples, and a
-- forward-only flag FAILS on go-past-and-come-back paths. G being an involution, the repair fires it
-- on crossings in EITHER direction; all eight side-of-readout cases close on G^2 = id + the shear
-- frozen right of readout (swapEvolve_comp).
-- swapEvolve_measurePreserving: the FULL propagator preserves the Liouville measure at every time
-- pair. swap_correlates / swap_pointerInvariant: both hypotheses discharged again, now on the
-- enlarged arena. Supporting Mathlib-dir lemmas (upstream candidates, CSD-free):
-- measurable_of_partition, measurePreserving_of_partition, Measure.map_eval_pi',
-- measurePreserving_swapSlot (via piFinSuccAbove -- a subtype-free split avoiding a Fintype
-- instance diamond).
-- ★★ swap_luders_marginal (SwapLuders.lean): CONDITIONED ON OUTCOME i, THE POST-MEASUREMENT SYSTEM
-- MARGINAL IS THE SLOT-i CALIBRATION -- map projSys (postMeasure mu_in i) = nu i. Collapse as
-- measure-preserving RELOCATION: nothing shrinks, the involution exchanges Liouville volume 1:1, and
-- what moves is WHICH NULL SLICE the epistemic measure occupies. Slot i afterwards holds the
-- PRE-measurement state and the depleted fibre -- a perfect ontic memory; irreversibility enters
-- only at slot RESET (erasure, priced by collapse_accuracy_bound).
-- ★★ swap_luders_born: with slots calibrated to the vertex preparations epistemicMeasure [e_j], the
-- post-outcome-i system marginal IS epistemicMeasure [e_i], so for ANY context field c' the
-- follow-up outcome-j probability is c'.rate [e_i] j -- THE BORN WEIGHTS OF THE COLLAPSED STATE.
-- Sequential statistics are Luders at rank one.
-- ⚠️ SCOPE. (1) NONDEGENERATE ONLY: at rank one the Luders channel IS measure-and-reprepare (a
-- standard QI fact -- the objection "that is reprepare, not collapse" applies identically to the
-- textbook channel); for DEGENERATE projectors it is NOT, and this witness does not cover them.
-- (2) The calibration nu_j = epistemicMeasure [e_j] is a CONTEXT-FIXED EPISTEMIC POSIT, parallel to
-- pointer-readiness, basis-dependent only, never psi-dependent -- A7-compatible -- and its
-- Liouville-nullity is FORCED by no_exact_collapse. (3) ONE MEASUREMENT CONSUMES ONE BANK; reset =
-- erasure, outside the protocol. (4) The Hamiltonian generation of the swap stage is STATED, NOT
-- FORMALISED, as for the shear. (5) The Luders CHANNEL-level bridge to LF5's operational result
-- (rho -> Pi rho Pi / Tr) is the rank-one reading recorded in the docstring, not a corpus theorem.
/-- info: 'CSD.RecordLayer.no_exact_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.no_exact_collapse

/-- info: 'CSD.RecordLayer.collapse_accuracy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.collapse_accuracy_bound

/-- info: 'MeasureTheory.measurePreserving_swapSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.measurePreserving_swapSlot

/-- info: 'CSD.RecordLayer.measurePreserving_swapG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurePreserving_swapG

/-- info: 'CSD.RecordLayer.swapEvolve_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swapEvolve_comp

/-- info: 'CSD.RecordLayer.swapEvolve_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swapEvolve_measurePreserving

/-- info: 'CSD.RecordLayer.swap_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_correlates

/-- info: 'CSD.RecordLayer.swap_pointerInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_pointerInvariant

/-- info: 'CSD.RecordLayer.swap_luders_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_luders_marginal

/-- info: 'CSD.RecordLayer.swap_luders_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_luders_born

-- DEGENERATE LUDERS: THE PROBLEM MADE PRECISE, THE BOUNDARY PROVED (2026-08-02,
-- SigmaLayer/DegenerateLuders.lean).
-- At rank one the Luders channel IS measure-and-reprepare and swap_luders_born delivers it. At
-- higher rank the post-state is the NORMALISED PROJECTION [Pi_i psi] -- psi-DEPENDENT, coherence
-- inside the block intact -- and that dependence is the whole difficulty. This module does three
-- things and claims no fourth:
-- (1) BlockLudersObligation -- the degenerate demand as a _statement Prop (CONVENTIONS 8.3):
-- post-outcome-i marginal = epistemicMeasure [Pi_i psi]. NOTHING in the corpus inhabits it for a
-- block of dimension >= 2.
-- (2) ★★ swap_not_blockLuders -- THE BOUNDARY, AS A THEOREM: the calibrated-swap witness fails the
-- obligation for ANY fixed calibration nu, whenever a block has dimension >= 2. The proof turns
-- swap_luders_marginal's virtue against it: the swap's post-marginal is the FIXED slot state nu i,
-- preparation-independent, while the obligation at two vertex preparations inside the block demands
-- the two DISTINCT states epistemicMeasure [e_j1] != epistemicMeasure [e_j2]
-- (vertexPoint_injective + epistemicMeasure_injective). So the fixed-calibration architecture is
-- REFUTED for degenerate measurements -- a machine-checked scope boundary, not a scope note.
-- (3) ★ degenerate_selector_born -- THE POSITIVE HALF THAT SURVIVES: the block-selector
-- (blockIndex b = b . basinIndex) has outcome sectors carrying EXACTLY the coarse-grained Born
-- weights, the dynamical realisation of OutcomeField's kinematic blockField. STATISTICS generalise
-- to degenerate measurements; the UPDATE is what does not.
-- Supporting: momentMap_vertex (the moment map at a vertex is its indicator -- also what makes
-- vertex_outcome_pos work), vertexPoint_injective, epistemicMeasure_injective.
-- ⚠️ WHAT REMAINS OPEN: the degenerate witness itself. It must relocate [psi] -> [Pi_i psi] -- a
-- psi-dependent target -- while preserving measure; no_exact_collapse still governs, so the lost
-- base data must be STORED. Route: the projective-join decomposition of CP^{N-1}, wall = the FS
-- measure decomposition under the join, unformalised geometry, effort L. specs/BACKLOG.md.
/-- info: 'CSD.RecordLayer.momentMap_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.momentMap_vertex

/-- info: 'CSD.RecordLayer.degenerate_selector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.degenerate_selector_born

/-- info: 'CSD.RecordLayer.vertex_outcome_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.vertex_outcome_pos

/-- info: 'CSD.RecordLayer.swap_not_blockLuders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_not_blockLuders

-- A5 STEP ONE: THE DUHAMEL BOUND (2026-08-02, Mathlib/Analysis/Matrix/DuhamelBound.lean).
-- The quantitative engine of (eps,T)-projectability: for skew-Hermitian generators,
-- ||exp(tC) - exp(tA)|| <= |t| ||C - A|| in the L2 operator norm; Hermitian corollary
-- ||exp(t(-iH)) - exp(t(-iH_0))|| <= |t| ||H - H_0||. Proved WITHOUT integrals: the interpolant
-- phi(s) = exp(sC) exp((t-s)A) has derivative exp(sC)(C-A)exp((t-s)A), of norm <= ||C-A|| because
-- both exponential factors are UNITARY (l2_opNorm_exp_smul_skew, from StoneC1's unitarity + the
-- L2 norm being a C*-norm), and the mean-value inequality finishes. CSD-free, upstream candidate.
-- READING FOR A5: a Hamiltonian eps-close in operator norm to a sector-projectable one generates
-- dynamics that sector dynamics SHADOWS to within eps*T over [-T, T] -- what makes a Hamiltonian
-- QUANTUM-EFFECTIVE. The predicate + exact-case-iff + shadowing packaging is the next step
-- (SigmaLayer/ApproxProjectability.lean, not yet written).
/-- info: 'Matrix.l2_opNorm_exp_smul_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.l2_opNorm_exp_smul_skew

/-- info: 'Matrix.norm_exp_smul_sub_exp_smul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_exp_smul_sub_exp_smul_le

/-- info: 'Matrix.norm_exp_smul_neg_I_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_exp_smul_neg_I_sub_le

-- A5 STEP TWO: THE (eps,T)-PROJECTABILITY PACKAGE (2026-08-02,
-- SigmaLayer/ApproxProjectability.lean) -- the BACKLOG ★ A5 row's stated shape, delivered.
-- EpsProjectable: the predicate on ontic Hamiltonians Sigma -> R in OSCILLATION form -- Hs varies by
-- at most eps along each fibre of pi. ⚠️ The DERIVATIVE form sup||d(deltaH)|_V|| <= eps is the
-- scoped manifold statement (section 2a; no exterior-calculus API); the oscillation form is its
-- formalisable core, and the substitution is stated wherever it appears, not made silently.
-- epsProjectable_zero_iff: THE EXACT CASE IS THE eps = 0 INSTANCE, AS AN IFF -- zero
-- fibre-oscillation is precisely factoring through pi, tying the new predicate to the corpus's
-- existing exact-case formalisation (kSectorDataFlow_projectable).
-- diagOnticEnergy_epsProjectable: NON-VACUITY -- the moment-map energy of a diagonal observable
-- (the ontic form of <psi, diag(lam) psi>) is an EpsProjectable _ 0 witness: the corpus's own
-- Born-weight energies are exactly projectable.
-- ★ quantum_effective_shadowing (+ _state): THE DYNAMICAL CONTENT. ||H - H_0|| <= eps and |t| <= T
-- give ||e^{t(-iH)} - e^{t(-iH_0)}|| <= eps*T (and eps*T*||psi|| on states). Since H_0's witness
-- flow is projectable (the exact case), THE SECTOR DYNAMICS TRACKS THE TRUE DYNAMICS TO WITHIN
-- eps*T -- for times up to T the sector cannot tell a quantum-effective Hamiltonian from its
-- projectable part. That is what "selects the sector" means operationally, and it is the content
-- the exact case alone could not express.
-- ⚠️ SCOPE: the shadowing lives on the HILBERT side, where the corpus's dynamics genuinely runs;
-- the ontic predicate lives on Sigma. The bridge -- an ontic Hamiltonian GENERATING a flow whose
-- projection is e^{-itH} -- is A2's open row, not A5's, and is not claimed.
/-- info: 'CSD.RecordLayer.epsProjectable_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.epsProjectable_zero_iff

/-- info: 'CSD.RecordLayer.diagOnticEnergy_epsProjectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.diagOnticEnergy_epsProjectable

/-- info: 'CSD.RecordLayer.quantum_effective_shadowing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.quantum_effective_shadowing

/-- info: 'CSD.RecordLayer.quantum_effective_shadowing_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.quantum_effective_shadowing_state

-- A2'S FORMALISABLE HALF: THE HAMILTONIAN SIGNATURE (2026-08-02,
-- SigmaLayer/HamiltonianSignature.lean).
-- A2 as written -- the flow is generated by X_H = w^{-1} dH -- needs the symplectic form and
-- exterior derivative: the section-2a-scoped manifold gap (verified a tooling gap, not a falsity).
-- What a measure space CAN express is the SIGNATURE a Hamiltonian flow leaves, and the witness flow
-- is shown to have every piece:
-- (1) A CANONICAL CONSERVED ENERGY. onticEnergy H = the base-point expectation re<psi,H psi>/||psi||^2,
-- well-defined on rays (baseEnergy_mk, the same quotient-descent as momentMap), invariant under any
-- unitary commuting with H (baseEnergy_smul_invariant: <Uv,HUv> = <v,(U*HU)v> = <v,Hv> plus unitary
-- norm preservation), hence CONSERVED BY THE WITNESS FLOW (onticEnergy_flow_invariant -- the
-- Schrodinger unitary is exp((-it)H), which commutes with H). The flow conserves its own generator:
-- the first Hamiltonian signature.
-- (2) ★ THE A5 JUNCTION. onticEnergy H is fibre-independent by construction, so it is
-- EpsProjectable _ 0 (onticEnergy_epsProjectable): it IS the canonical h of the exact case
-- H = h.pi. A2's conserved quantity and A5's projectable Hamiltonian are the SAME OBJECT.
-- (3) THE COMMUTING PHASE TORUS. phaseDiag phi = diag(e^{i phi_k}) is unitary; the action is
-- additive hence commuting (phaseDiag_add / phaseDiag_comm) and PRESERVES EVERY MOMENT-MAP
-- COORDINATE (momentMap_phaseDiag_invariant) -- the flow-level shadow of "the moment map generates
-- the torus action" (the generating statement needs the symplectic form; scoped). The fibre half of
-- the torus signature is ShearWitness's pshift translations, measure-preserving, already in place.
-- Together with the Liouville property and group laws already proved of the witness flow, the
-- honest claim: EVERY property of "Hamiltonian flow" expressible without the manifold API is proved
-- of the witness flow; the vector-field equation itself is scoped. A2's unscoped content is
-- discharged; what remains of A2 is exactly its scoped half.
/-- info: 'CSD.RecordLayer.baseEnergy_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.baseEnergy_mk

/-- info: 'CSD.RecordLayer.baseEnergy_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.baseEnergy_smul_invariant

/-- info: 'CSD.RecordLayer.onticEnergy_flow_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.onticEnergy_flow_invariant

/-- info: 'CSD.RecordLayer.onticEnergy_epsProjectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.onticEnergy_epsProjectable

/-- info: 'CSD.RecordLayer.momentMap_phaseDiag_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.momentMap_phaseDiag_invariant

/-- info: 'CSD.RecordLayer.phaseDiag_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.phaseDiag_comm

-- A6 STEP ONE: THE SEGRE EMBEDDING AND NON-FACTORISATION (2026-08-02,
-- SigmaLayer/OnticComposite.lean).
-- Paper C A6's "the composite ontic sector is NOT the product of the subsystem sectors" made sharp:
-- segre ([u],[v]) = [u (x) v] is INJECTIVE (segre_injective -- product rays remember their factors;
-- the scalar is recovered from a nonzero coordinate of the other factor) but NOT SURJECTIVE
-- (segre_not_surjective) whenever both factors have dimension >= 2: the Bell-type ray
-- [e0(x)e0 + e1(x)e1] is not a product ray -- the four corner coordinates give u0v0 = c, u1v1 = c,
-- u0v1 = 0, u1v0 = 0, and (u0v0)(u1v1) = c^2 != 0 = (u0v1)(u1v0). Hence
-- Sigma_AB STRICTLY EXCEEDS image(Sigma_A x Sigma_B): non-factorisation as a THEOREM, at every
-- dimension pair >= 2x2.
-- ⚠️ SCOPE: witness-level A6 content. The corpus CONSTRUCTS the composite sector from the composite
-- Hilbert space; A6-as-philosophy ("Sigma_AB is primitive") is not a formalisation target and is not
-- claimed. Steps 2-3 (ontic reduction maps via partialTrace; marginal stability under local flows =
-- ontic no-signalling) are NOT in the file. Measure statements (Segre image mu_FS-null) not
-- attempted; the strict inclusion carries the axiom's weight.
/-- info: 'CSD.RecordLayer.segre_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.segre_mk

/-- info: 'CSD.RecordLayer.segre_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.segre_injective

/-- info: 'CSD.RecordLayer.segre_not_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.segre_not_surjective

-- A6 STEPS TWO AND THREE: ONTIC REDUCTION MAPS + MARGINAL STABILITY (2026-08-02,
-- SigmaLayer/OnticMarginals.lean).
-- STEP 2: rayDensity -- the density matrix of a composite ray, RAY-WELL-DEFINED (rayDensity_mk, the
-- quotient-descent pattern) and UNIT TRACE (rayDensity_trace): a genuine state. reduceA / reduceB:
-- the subsystem marginals as partial traces -- the ontic-level r_S, what a subsystem observer can
-- see of a single composite point.
-- STEP 3: actA U -- the local A-action (U (x) 1) in vector form, no Kronecker plumbing. The
-- workhorse is actA_column_sums: for U^H U = 1 the A-sums of transformed products equal the A-sums
-- of the originals, for EVERY pair of B-indices -- one computation carrying the norm preservation
-- (norm_actA) and both marginal laws:
-- ★★ reduceB_pointA_invariant  MARGINAL STABILITY = ONTIC NO-SIGNALLING: a local unitary on A
--                              leaves the B-marginal of the composite ray UNCHANGED. Acting on A
--                              changes nothing B can see, at the level of the single ontic point --
--                              the ontic form of the operational tensorSector_no_signalling.
-- reduceA_pointA_conj          the A-marginal evolves by CONJUGATION -- the Heisenberg law.
-- ★★ reduceB_local_flow_invariant  the Schrodinger flow of ANY A-Hamiltonian leaves the B-marginal
--                              fixed AT EVERY TIME -- A6's marginal-stability clause in flow form.
-- ⚠️ SCOPE: kinematic identities about the reduction maps under local unitaries -- exactly what
-- A6's clause asserts; no new dynamics claimed. Step 4 (DYNAMICAL no-signalling through the v0.7.0
-- measurement layer) is NOT here. Defined at the projective level; the torus fibre plays no role in
-- reduction.
-- WITH THIS, EVERY A6 CLAUSE THE CORPUS CAN EXPRESS IS A THEOREM: non-factorisation (step 1),
-- reduction maps (step 2), marginal stability (step 3). The A1-A7 map has NO unscoped open rows
-- left.
/-- info: 'CSD.RecordLayer.rayDensity_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.rayDensity_trace

/-- info: 'CSD.RecordLayer.actA_column_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.actA_column_sums

/-- info: 'CSD.RecordLayer.reduceB_pointA_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.reduceB_pointA_invariant

/-- info: 'CSD.RecordLayer.reduceA_pointA_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.reduceA_pointA_conj

/-- info: 'CSD.RecordLayer.reduceB_local_flow_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.reduceB_local_flow_invariant

-- THE FIRST DYNAMICAL EMPIRICAL ENTRY (2026-08-02, Empirical/CSD/SequentialMeasurement.lean).
-- Every other empirical entry exercises the KINEMATIC Born machinery; this one exercises the
-- MEASUREMENT DYNAMICS -- the calibrated-swap witness -- and two textbook empirical facts fall out
-- as consequences rather than separate posits:
-- ★★ csd_repeatability (+ _same/_other): measure in the computational basis, obtain i, measure
-- again in the SAME basis -- outcome i recurs with probability 1, every other outcome 0. Von
-- Neumann repeatability, DERIVED from swap_luders_born + momentMap_vertex (the follow-up context's
-- rate at the collapsed vertex is the vertex's indicator).
-- ★ csd_sequential_born: after outcome i, follow-up statistics for ANY context field c' are the
-- COLLAPSED state's Born weights c'.rate [e_i] -- the preparation has left the statistics. The
-- Luders update as an empirical prediction.
-- ⚠️ Rank-one computational-basis first measurement (the swap witness's scope); hpos carried as a
-- hypothesis (conditioning on a null outcome is undefined, as it should be); inherits the witness's
-- calibration-posit and Hamiltonian-origin scope notes.
/-- info: 'CSD.Empirical.CSDBridge.SequentialMeasurement.csd_sequential_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SequentialMeasurement.csd_sequential_born

/-- info: 'CSD.Empirical.CSDBridge.SequentialMeasurement.csd_repeatability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SequentialMeasurement.csd_repeatability

/-- info: 'CSD.Empirical.CSDBridge.SequentialMeasurement.csd_repeatability_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SequentialMeasurement.csd_repeatability_same

-- KCBS PENTAGON BORN WEIGHTS AS KAHLER VOLUMES (2026-08-02,
-- Empirical/CSD/Contextuality/KCBSVolume.lean) -- closing the audit's KCBS gap, the last flagship
-- test without a CSD twin.
-- The representative pentagon context {kv 0, kv 1} is completed to a projective frame by the CROSS
-- PRODUCT kv 0 x kv 1 (orthogonal to both by dot_self_cross/dot_cross_self, unit by the Lagrange
-- identity cross_dot_cross: 1*1 - 0^2 = 1), complexified via the transport c3_inner -- every
-- orthonormality fact PULLED from the QM side's real dot products (kv_orth, kv_unit), nothing
-- re-proved. kcbsContextBasis is the resulting OrthonormalBasis; the engine
-- context_born_frequency_volume instantiates at it: every ray's context-dependent Born weight is
-- the a.s. frequency limit of its barycentric Born region on the fixed ontic Sigma = CP^2 -- an FS
-- typicality volume. kcbs_pentagon_weight: at the apex preparation the ray-0 weight is the pentagon
-- number 1/sqrt(5) -- the quantity whose five-fold sum sqrt(5) violates the noncontextual bound 2
-- (kcbs_quantum_violation). The _canonical form discharges the trial bundle on fsTrialMeasure.
-- ⚠️ One representative context built (KS18Volume discipline): the other four are identical
-- instantiations, orthogonality already certified for all five adjacencies by kv_orth. Realisation
-- not derivation; Phi = id; the inequality itself stays at the QM layer.
/-- info: 'CSD.Empirical.CSDBridge.KCBS.kcbs_pentagon_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KCBS.kcbs_pentagon_weight

/-- info: 'CSD.Empirical.CSDBridge.KCBS.kcbs_context_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KCBS.kcbs_context_born_frequency_volume

/-- info: 'CSD.Empirical.CSDBridge.KCBS.kcbs_context_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KCBS.kcbs_context_born_frequency_volume_canonical

-- THE QUANTUM ERASER TWIN, VIA THE RECORD ROUTE (2026-08-02, Empirical/CSD/QuantumEraserVolume.lean).
-- The eraser's signature is a VANISHING conditional probability (the dark fringe), which the
-- Duistermaat-Heckman route's ORIGINAL lemmas could not state (hpos) -- corrected 2026-08-02: the _uncond engine (2026-06-11) does state zeros; the record route stands by choice. Like
-- HongOuMandelVolume, this twin lives on the record layer, where a zero rate is a zero-width cell:
-- ★ eraser_fringe_typicality: the full-visibility conditioned fringe (1 + c·cos φ)/2 is a fibre
-- typicality volume at EVERY phase, boundary values included.
-- ★ eraser_dark_typicality_zero (+ _record_null, _measurement_zero): at φ = π the dark cell is
-- exactly null -- no microstate of Σ produces a dark-port detection; nothing cancels across runs.
-- ★ eraser_dark_basin_null: the same zero at the v1.0 context-fixed basin layer -- at the dark point
-- the conditioned state IS the vertex [e₁] (mk_eraserOut_pi), and the dark basin's fibre arc has
-- width 0 there (globalBasin_prob + momentMap_vertex, the repeatability lemmas).
-- eraserOut_rate_conditional ties the rates to the QM module: joint over marker marginal, both
-- sides QM-side quantities -- the conditioned state is derived, not asserted.
-- ⚠️ Realises the conditioned STATISTICS ontically; the conditioning PROCESS (marker measurement as
-- swap-witness dynamics on the composite) needs the unitary-covariance extension (BACKLOG).
/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_fringe_typicality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_fringe_typicality

/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_typicality_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_typicality_zero

/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_record_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_record_null

/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_basin_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraser_dark_basin_null

/-- info: 'CSD.Empirical.CSDBridge.QuantumEraserVolume.eraserOut_rate_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumEraserVolume.eraserOut_rate_conditional

-- BB84 INTERCEPT-RESEND WITH A DYNAMICAL COLLAPSE STEP (2026-08-02,
-- Empirical/CSD/Crypto/BB84Sequential.lean + SigmaLayer/RotatedContext.lean).
-- The QM module (Crypto/BB84.lean) models Eve's measure-and-resend as a CLASSICAL MARGINAL, with a
-- scope note gating the collapse operator on "the LF5 gate". The dynamical measurement layer
-- dissolved that gate; this entry replaces the posited marginal with the calibrated-swap dynamics:
-- ★ basisContext_rate_mk (RotatedContext): the context field of an apparatus measuring in ANY
-- orthonormal basis, rates = rotated Born weights ‖⟨b i, ψ⟩‖² -- the unitary-covariance seed. With
-- it, csd_sequential_born extends to CROSS-BASIS follow-ups.
-- ★ prep_outcome_pos (SequentialMeasurement): for the canonical ready preparation, hpos is a
-- THEOREM whenever the Born weight is nonzero -- conditioning licensed by the preparation, the
-- carried-hypothesis caveat discharged at every concrete preparation.
-- ★ bb84_wrong_basis_bob (+ _error): Alice sends |+>, Eve Z-measures (the swap witness's native
-- basis), Bob reads the rotated X-context: every Bob basin has probability EXACTLY 1/2 whatever
-- Eve saw -- the 1/2 disturbance with the collapse a pushforward theorem. Both measurements are
-- context-field reads of the dynamical layer: the sequential composition is end-to-end.
-- ★ bb84_right_basis_no_disturbance / _faithful: Eve in the matching basis is exactly
-- repeatability -- error basin null, correct basin certain. Eve learns the bit and disturbs nothing.
-- bb84_eve_selector_born: Eve's outcome weights on |+> are a fair coin (the information side).
-- ⚠️ Dual round of the QM module's (Alice X / Eve Z, so Eve is computational-basis); one sifted
-- round; Eve's basis choice + the 1/4 average stay classical bookkeeping on the QM side
-- (bb84_dynamical_matches_marginal records the correspondence); composable finite-key remains the
-- recorded QKD tranche.
/-- info: 'CSD.RecordLayer.basisContext_rate_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.basisContext_rate_mk

/-- info: 'CSD.RecordLayer.prep_outcome_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
-- (moved 2026-08-02 from Empirical/CSD/SequentialMeasurement.lean to SigmaLayer/SwapClosure.lean)
#print axioms CSD.RecordLayer.prep_outcome_pos

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_eve_selector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_eve_selector_born

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_wrong_basis_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_wrong_basis_bob

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_right_basis_no_disturbance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_right_basis_no_disturbance

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_right_basis_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_right_basis_faithful

-- B92 AND WIESNER SEQUENTIAL TWINS (2026-08-02, Empirical/CSD/Crypto/{B92,Wiesner}Sequential.lean).
-- Instantiations of the BB84Sequential engine, recorded as such -- the dynamical fact is the same
-- calibrated-swap composition, re-read on each protocol's semantics:
-- B92: ★ b92_honest_false_click_null -- unambiguity as a NULL BASIN (a |+> carrier has a zero-width
-- conclusive-bit-0 arc; the eraser-dark-fringe shape); ★ b92_eve_false_click -- after Eve's
-- Z-intercept the false-click basin is exactly 1/2 whatever she recorded; ★ b92_eve_detectable --
-- the strict contrast (intercept raises false clicks strictly above the honest zero).
-- Wiesner: ★ wiesner_forge_x_pass_half / _caught_half -- the measure-resend counterfeit passes a
-- conjugate-basis position with probability exactly 1/2 (collapse = pushforward theorem);
-- ★ wiesner_forge_z_invisible -- matching basis = repeatability, the forger copies for free (the
-- mint's secret basis IS the security); wiesner_rate_eq_verifyProb ties the ontic pass rate to the
-- QM module's verifyProb; the 3/4 = (1/2)(1) + (1/2)(1/2) per-position average is the (3/4)^n
-- counterfeiting value -- ⚠️ ATTAINED by measure-resend here; optimality (Molina-Vidick-Watrous
-- 2012) out of scope. Both inherit the calibrated-swap scope notes.
/-- info: 'CSD.Empirical.CSDBridge.B92Sequential.b92_honest_false_click_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.B92Sequential.b92_honest_false_click_null

/-- info: 'CSD.Empirical.CSDBridge.B92Sequential.b92_eve_false_click' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.B92Sequential.b92_eve_false_click

/-- info: 'CSD.Empirical.CSDBridge.B92Sequential.b92_eve_detectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.B92Sequential.b92_eve_detectable

/-- info: 'CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_forge_x_pass_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_forge_x_pass_half

/-- info: 'CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_forge_z_invisible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_forge_z_invisible

/-- info: 'CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_rate_eq_verifyProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WiesnerSequential.wiesner_rate_eq_verifyProb

-- THE MEASUREMENT PROPAGATOR IS PROVABLY NOT CONTINUOUS (2026-08-02,
-- SigmaLayer/ShearDiscontinuity.lean; machine-checks an external review's claim).
-- ★ shearEvolve_not_continuous: over the measurement interval the shear witness displaces the
-- register by shearAmt(basinIndex x); if continuous, its register marginal would be a continuous
-- map from the CONNECTED KSigma onto >= 2 distinct points, whose fibres give a clopen partition --
-- impossible. Consequence: the witness is a measurable, measure-preserving, PIECEWISE map, not a
-- time slice of any continuous flow -- so the earlier "Hamiltonian generation = permanently scoped
-- (Mathlib gap)" classification was misjustified and is REOPENED (specs/BACKLOG.md). Context that
-- keeps this honest in both directions: no_everywhere_correlation already proves SOME seam set is
-- forced for every exact-record dynamics -- the witness's jumps sit exactly where the no-go says
-- they must. Supporting: ℂℙ^{N-1} is CONNECTED (staged connectedSpace_of_isConnected_nonzero via
-- isConnected_compl_singleton_of_one_lt_rank at real rank 2N); vertex basin inhabitants; pairwise
-- distinct shear displacements.
/-- info: 'CSD.RecordLayer.shearEvolve_not_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shearEvolve_not_continuous

/-- info: 'CSD.RecordLayer.vertex_mem_globalBasin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.vertex_mem_globalBasin

/-- info: 'Projectivization.connectedSpace_of_isConnected_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.connectedSpace_of_isConnected_nonzero

-- THE PIECEWISE-HAMILTONIAN CLASSIFICATION (2026-08-02, SigmaLayer/PiecewiseHamiltonian.lean;
-- the decision resolving the reopened Hamiltonian-origin row -- route 2, user decision).
-- ★ shear_piecewise_hamiltonian: (1) on every basin cylinder the propagator IS an explicit rigid
-- register translation -- a Hamiltonian flow slice -- and is ContinuousOn there
-- (shearEvolve_eq_translation_on_basin, shearEvolve_continuousOn_basin); (2) the seam set outside
-- the cylinders is NULL (seam_null, via globalBasin_ae_total through the product). Together with
-- shearEvolve_not_continuous (the seams are real) and no_everywhere_correlation (they are forced
-- for every exact-record dynamics): piecewise rigid SYMPLECTIC translation, null seam set.
-- CORRECTED 2026-08-04 (audit): this read "piecewise Hamiltonian" long after
-- PiecewiseHamiltonian.lean's header WITHDREW that reading (on T^2, iota_X omega = a*dp is
-- closed but NOT exact, so no global generator exists). The pieces are symplectic, not
-- Hamiltonian; the theorem name is a known misnomer kept for pin stability.
-- ⚠️ The h_i = shearAmt(i)·p_R reading of each piece is prose (the symplectic spelling is the
-- genuine §2a Mathlib gap); corridor regularisation stays recorded as optional strengthening.
/-- info: 'CSD.RecordLayer.shear_piecewise_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shear_piecewise_hamiltonian

/-- info: 'CSD.RecordLayer.shearEvolve_eq_translation_on_basin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.shearEvolve_eq_translation_on_basin

/-- info: 'CSD.RecordLayer.seam_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.seam_null

-- ALL SIX DYNAMICAL FACTS ON ONE ARENA (2026-08-02, SigmaLayer/SwapClosure.lean; the external
-- review's step 2, the precursor to the engine migration).
-- ★ swapMeasurementClosure: ready ⇒ no record, record created, outcomes exclusive, record persists,
-- DYNAMICAL Born (sector measure = Born weight, via measure_outcomeSector_eq_of_correlates -- the
-- correlation theorem genuinely consumed), and rank-one Lüders -- every field a swapProtocol
-- statement on SwapArena at the canonical preparation swapPrep [ψ]. CorrelatesOn/PointerInvariantOn
-- proved (swap_correlates/swap_pointerInvariant), never assumed. Lüders carries NO measure
-- hypothesis: Born-weight positivity licenses the conditioning (prep_outcome_pos, moved here from
-- the empirical layer). ⚠️ The OPERATIONAL closure still lives on its own arena -- CsdFiniteQMClosure
-- remains a two-arena conjunction; this removes the split within the DYNAMICAL bundle only. The
-- engine migration proper stays recorded (BACKLOG).
/-- info: 'CSD.RecordLayer.swapMeasurementClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swapMeasurementClosure

/-- info: 'CSD.RecordLayer.swap_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.swap_sector_born

-- ★★ THE ENGINE MIGRATION (2026-08-02, SigmaLayer/UnifiedArena.lean; review step 3 -- arena
-- unification step 2 of 2). ONE ontic model now carries the finite-QM reconstruction:
-- UnifiedArena M = ((ℂℙ^M × T²) × T²_R) × bank, with Liouville measure arenaLiouville =
-- swapMeasure at μs = kMuL -- so the measure the MEASUREMENT dynamics preserves IS the Liouville
-- measure the ISOLATED flow preserves (that coincidence is the migration's content).
-- ★★ unifiedArenaClosure: isolated exp(-itH) lifted to the arena preserves arenaLiouville
-- (arenaIso_measurePreserving) and projects to Schrödinger on rays (arenaIso_schrodinger); the
-- FS bridge holds through the arena marginals (arenaRay_pushforward); swapEvolve preserves the
-- SAME measure; the six dynamical facts hold (SwapMeasurementClosure field); i.i.d. Born
-- frequencies and mixed-state Born weights transfer through the system-slot marginal
-- (rfl-level cylinder identities). All ELEVEN operational fields accounted for in the module's
-- mapping table: migrated / upgraded / superseded-by-stronger / one recorded (mixed LLN, S).
-- ⚠️ CsdFiniteQMClosure (the two-arena conjunction) stays untouched as the historical capstone;
-- the composed round-trip theorem (isolate → measure → isolate) is recorded, not claimed.
/-- info: 'CSD.RecordLayer.unifiedArenaClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.unifiedArenaClosure

/-- info: 'CSD.RecordLayer.arenaIso_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arenaIso_measurePreserving

/-- info: 'CSD.RecordLayer.arenaIso_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arenaIso_schrodinger

/-- info: 'CSD.RecordLayer.arenaRay_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arenaRay_pushforward

-- THE MIGRATION RESIDUES, DISCHARGED SAME DAY (2026-08-02, UnifiedArena.lean second pass):
-- ★ arena_round_trip -- isolate → measure → isolate: the record is created from the evolved
-- state's selector and SURVIVES subsequent isolated evolution (readout_arenaIso: the pointer
-- register is a conserved coordinate of the lifted flow -- definitional, rfl). The first theorem
-- composing the Schrödinger and measurement propagators; not stateable before the migration.
-- arena_mixed_born_frequency -- the mixed two-stage LLN on the arena (rfl-level transfer).
/-- info: 'CSD.RecordLayer.arena_round_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arena_round_trip

/-- info: 'CSD.RecordLayer.arena_mixed_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.arena_mixed_born_frequency

-- DEGENERATE LÜDERS, THE JOIN ROUTE, BRICK 1 (2026-08-02, SigmaLayer/BlockCollapse.lean; review
-- step 4 opened). swap_not_blockLuders proved no FIXED calibration works; this brick builds the
-- object every witness must realise and the mechanism one level above the rays:
-- ★ blockCollapse -- the measurable ray-level collapse [ψ] ↦ [Πᵢψ] (quotient descent via
-- Projectivization.lift; measurability through measurable_iff_measurable_comp_mk').
-- ★ luders_target_eq_relocation + blockLudersObligation_iff_relocation -- COLLAPSE AS RELOCATION:
-- the §8.3 target epistemicMeasure [Πᵢψ] IS the pushforward of the preparation under the
-- deterministic relocation (base ray collapses, fibre untouched); the obligation is exactly the
-- demand that a witness realise this pushforward as its conditioned trace.
-- ★ componentSwap_collapse/_stores (+ _involutive, _norm_sum) -- the VECTOR-LEVEL witness core:
-- on ℂ^N ⊕ ℂ^N, keep block parts, swap complements: with a block-calibrated slot this performs
-- exactly the collapse WITH THE RESIDUAL STORED (no_exact_collapse respected by storage), and it
-- is involutive + summed-norm-preserving (the unitary content).
-- ⚠️ THE WALL, SHARPENED: the ray-pair version is ill-defined -- the stored residual depends on
-- the relative scale the product ℙ×ℙ quotient forgets (a surviving relative U(1) is needed).
-- Recorded routes: (i) FS disintegration under join coordinates; (ii) NEW -- a phase-carrying
-- slot (sphere-level bank), likely cheaper. swap_not_blockLuders remains the honest boundary;
-- NO ray-level witness is claimed.
/-- info: 'CSD.RecordLayer.luders_target_eq_relocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.luders_target_eq_relocation

/-- info: 'CSD.RecordLayer.blockLudersObligation_iff_relocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.blockLudersObligation_iff_relocation

/-- info: 'CSD.RecordLayer.componentSwap_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.componentSwap_collapse

/-- info: 'CSD.RecordLayer.measurable_blockCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurable_blockCollapse

-- ★★ THE PHASE-CARRYING SLOT: DEGENERATE LÜDERS REALISED (2026-08-02,
-- SigmaLayer/PhaseSlot.lean; route (ii) of the sharpened wall, brick 2).
-- ★★ phase_slot_block_luders: prepare the PHASE ORBIT of ψ (uniform over the ontic phase --
-- the enrichment adds ontic phase, not epistemic content: readout_phasePrep gives back the
-- Dirac at [ψ]); calibrate the slot with a FIXED block-supported α; fire the pair swap; read
-- out the system ray: the result is EXACTLY δ_{[Πᵢψ]} -- the blockLudersObligation target --
-- for every preparation with nonvanishing block component.
-- ★ pairSwap: TOTAL + INVOLUTIVE + MEASURABLE -- fire componentSwap exactly when both outputs
-- are nonzero; at a fired image the condition holds automatically (componentSwap involutive +
-- inputs nonzero), so the conditional map is a genuine involution: reversibility, hence
-- storage, hence no_exact_collapse respected.
-- WHY THE NO-GO IS EVADED, not contradicted: swap_not_blockLuders killed FULL swaps (post-
-- system = slot's prior content, preparation-independent); the PARTIAL swap keeps the system's
-- block part and stores its complement -- fixed calibration, preparation-dependent post-state.
-- The partial swap needed the phase-enriched arena, exactly as the sharpened wall said.
-- ⚠️ Brick 3 still owed (BACKLOG): register/sector protocol plumbing on the enriched arena +
-- Liouville preservation (unitarily-invariant reference measure, e.g. Gaussian; effort M).
/-- info: 'CSD.RecordLayer.phase_slot_block_luders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.phase_slot_block_luders

/-- info: 'CSD.RecordLayer.pairSwap_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.pairSwap_involutive

/-- info: 'CSD.RecordLayer.readout_phasePrep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.readout_phasePrep

/-- info: 'CSD.RecordLayer.measurable_pairSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurable_pairSwap

-- ★★ THE JOIN ARENA: LIOUVILLE-PRESERVING DEGENERATE LÜDERS (2026-08-02,
-- SigmaLayer/JoinArena.lean; brick 3's Liouville half). The identification that closes the arc:
-- THE PHASE-ENRICHED PAIR ARENA IS THE PROJECTIVE JOIN ℙ(ℂ^{N+N}) -- a system-slot pair
-- quotiented only by the GLOBAL phase, so the relative phase (the join coordinate the wall
-- demanded) lives in the point itself. There the component swap is a PERMUTATION UNITARY
-- (joinMat_mem_unitaryGroup), and:
-- ★★ joinSwap_measurePreserving -- Liouville preservation = Fubini-Study unitary invariance,
-- discharged by fubiniStudyMeasure_smul_invariant. The obligation recorded as the route's hard
-- half is a ONE-LINE consequence of the dynamics being unitary.
-- ★★ join_block_luders -- the Lüders update POINTWISE: every join microstate [ψ ⊕ α] with
-- nonvanishing block component and block-supported slot reads out post-swap to EXACTLY [Πᵢψ].
-- Deterministic at every microstate; PhaseSlot's measure form is the orbit-averaged shadow.
-- (The slot's nonvanishing is not even needed -- the hypothesis list is minimal.)
-- ⚠️ Remaining (BACKLOG, mechanical M): the register/sector MeasurementProtocol on
-- ℙ(ℂ^{N+N}) × T²_R firing joinSwap, mirroring SwapWitness. No new mathematics.
/-- info: 'CSD.RecordLayer.join_block_luders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.join_block_luders

/-- info: 'CSD.RecordLayer.joinSwap_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinSwap_measurePreserving

/-- info: 'CSD.RecordLayer.joinMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinMat_mem_unitaryGroup

/-- info: 'CSD.RecordLayer.measurable_joinFst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurable_joinFst

-- THE DEGENERATE MEASUREMENT AS A MeasurementProtocol (2026-08-02, SigmaLayer/JoinProtocol.lean;
-- brick 4 -- the protocol plumbing). The join update now runs inside the standard architecture:
-- arena = (join point, system fibre, ANCILLA fibre) x register; selector = coarse block index
-- (joinIdx); propagator = register shear + record-triggered joinG at the readout crossing (join
-- unitary on the point + system-fibre/ancilla-fibre exchange -- the degenerate analogue of the
-- rank-one fresh slot: the original fibre is STORED, not destroyed). Region/readout/sector/
-- persistence machinery inherited from shearProtocol by structure update.
-- ★ joinEvolve_measurePreserving -- the FULL propagator preserves the join-arena Liouville
-- measure (FS x vol x vol) x vol at every time pair (generic shear theorem + FS unitary
-- invariance + the fibre-transposition shuffle, glued by the register-arc partition).
-- join_correlates / join_pointerInvariant discharged from the construction; joinG_joinG is the
-- involution (reversibility = storage). ⚠️ Brick 5 (last): the sector-conditioned post-marginal
-- = epistemicMeasure [Πᵢψ] -- the BlockLudersObligation instance (BACKLOG).
/-- info: 'CSD.RecordLayer.joinEvolve_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinEvolve_measurePreserving

/-- info: 'CSD.RecordLayer.join_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.join_correlates

/-- info: 'CSD.RecordLayer.join_pointerInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.join_pointerInvariant

/-- info: 'CSD.RecordLayer.joinG_joinG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinG_joinG

-- ★★ BlockLudersObligation, INHABITED (2026-08-02, SigmaLayer/JoinLuders.lean; brick 5 -- the
-- degenerate-Lüders arc CLOSED). The §8.3 demand that swap_not_blockLuders proved impossible for
-- every fixed ray-level calibration is DELIVERED by the join witness:
-- ★★ joinWitness_blockLuders -- with any block-supported calibration family, the sector-
-- conditioned post-measurement system readout equals epistemicMeasure [Πᵢψ] for EVERY preparation
-- with nonvanishing block component. ψ-dependent post-states from a FIXED calibration, through
-- Liouville-preserving dynamics inside the standard MeasurementProtocol architecture.
-- ★ join_luders_marginal -- the computation: conditioning commutes with the preparation
-- pushforward (cond_map); the sector pulls back to a SYSTEM-FIBRE cylinder (the phase orbit has
-- constant ray, so the selector never sees the phase); product conditioning factorises
-- (cond_prod_prod); on the conditioned support the readout is [Πᵢψ] at every phase with the
-- ANCILLA's fibre; the conditioned original fibre integrates out -- stored, not destroyed.
-- goodTheta_vol_pos: positivity from Πᵢψ ≠ 0 alone -- the obligation carries NO measure
-- hypothesis. The rank-one (SwapLuders) and degenerate (here) updates now stand on the same
-- architectural footing; swap_not_blockLuders stands as the theorem for WHY the ray-pair arena
-- was too small.
/-- info: 'CSD.RecordLayer.joinWitness_blockLuders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.joinWitness_blockLuders

/-- info: 'CSD.RecordLayer.join_luders_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.join_luders_marginal

/-- info: 'CSD.RecordLayer.goodTheta_vol_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.goodTheta_vol_pos

-- (conditioning toolkit moved to CsdLean4/Mathlib/Probability/ConditionalProbability.lean,
-- 2026-08-02 -- the S-item extraction for upstream)
/-- info: 'ProbabilityTheory.cond_prod_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.cond_prod_prod

/-- info: 'CSD.RecordLayer.basisContext_basisFun_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.basisContext_basisFun_rate

-- ★★ THE UNITARY-COVARIANCE LAW (2026-08-02, SigmaLayer/RotatedSwap.lean; the last extension
-- item of the dynamical arc). The first measurement now runs in ANY orthonormal basis:
-- ★★ measurement_covariance -- for EVERY orthonormal basis bON and every state, the full
-- six-fact measurement closure holds (RotatedSwapClosure): selector = the rotated context's
-- basins, bank calibrated on the rotated vertices [bON i], dynamical Born = ‖⟨bON i, ψ⟩‖²,
-- Lüders to [bON i]. The apparatus basis is a PARAMETER of the context field, not a preferred
-- structure of Σ. Pure instantiation: swap_luders_marginal was always selector- and
-- calibration-generic; the new content is the context-generic swap-arena accounting
-- (sector_born_ctx, prep_outcome_pos_ctx -- generalising the momentContext instances).
-- ★ bb84_primal_wrong_basis (BB84Sequential): the QM module's OWN round (Alice Z / Eve X /
-- Bob Z), end-to-end dynamical -- the dual-round caveat retired.
/-- info: 'CSD.RecordLayer.measurement_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.measurement_covariance

/-- info: 'CSD.RecordLayer.rotated_swap_luders_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.rotated_swap_luders_born

/-- info: 'CSD.RecordLayer.sector_born_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.RecordLayer.sector_born_ctx

/-- info: 'CSD.Empirical.CSDBridge.BB84Sequential.bb84_primal_wrong_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BB84Sequential.bb84_primal_wrong_basis

-- STEP FIVE (2026-07-29): THE (n-1)/n SUPPORT BOUND, as a theorem.
-- vanishes_below_of_balanced: given (a) step four's output -- for a.e. phi some outcome i has
-- g == 0 on [0, 1 - s_i(phi)] -- and (b) that states with ALL overlaps <= c are non-null for every
-- c above the forced minimum 1/n, the density VANISHES ON EVERY OVERLAP VALUE BELOW (n-1)/n.
-- The step is short for a structural reason worth noting: step four's conclusion is POINTWISE IN g
-- (g dies on a whole interval, for a.e. phi). g is a fixed function, so ONE suitable phi suffices
-- and no almost-everywhere bookkeeping survives into the conclusion -- hence the helper
-- exists_mem_of_measure_pos_of_ae (a positive-measure set meets any a.e. property) is all that is
-- needed to bridge measure to pointwise.
-- At n = 2 the bound reads "g vanishes below 1/2", exactly the support of the known solution
-- 4(2s-1)+ -- sharp at the one dimension where a solution exists.
-- STILL CONDITIONAL for mu_FS on hypothesis (b): the balanced-state abundance. Its proof shape is
-- settled (barycentre box, side min(b,c-b)/(M+1)) but was NOT landed 2026-07-29 -- see the note in
-- ContextFixedA7FS.lean and the BACKLOG row. Not stubbed, not claimed.
/-- info: 'CSD.SigmaLayer.exists_mem_of_measure_pos_of_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.exists_mem_of_measure_pos_of_ae

/-- info: 'CSD.SigmaLayer.vanishes_below_of_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.vanishes_below_of_balanced

-- STEP FOUR (2026-07-29): ORTHOGONAL PREPARATIONS -- the first GENERIC-psi input.
-- Steps one to three used only the n basis-vector preparations. This uses psi PERPENDICULAR to
-- e_i: the Born weight |<e_i|psi>|^2 is then zero, so the same nonnegativity argument applies --
-- but now for a whole FAMILY of psi rather than one. orthogonal_preparation_vanishes: on Omega_i
-- the density vanishes at every overlap value any such psi realises.
-- vanishes_on_interval_of_dense upgrades that from the realised values to an INTERVAL, given
-- continuity of g and density of the realised values. The geometric input: for unit psi in the
-- sphere of e_i-perp, |<psi|phi>|^2 is maximised at the normalised projection of phi into
-- e_i-perp with value 1 - s_i(phi), and tilting psi within e_i-perp sweeps continuously down to 0.
-- ★ THAT TILT NEEDS dim(e_i-perp) >= 2, i.e. N >= 3 -- at N=2 the orthocomplement is a LINE, psi
-- is unique up to phase, and only the single value 1 - s_i(phi) is realised. Same threshold as
-- steps two and three, for a THIRD independent reason.
-- Consequence (analysis, not yet formalized -- the covering + max-coordinate step remains):
-- g vanishes below (n-1)/n, sharpening the cap from 1/2. At n=2 that reads "below 1/2", which is
-- exactly where the known solution 4(2s-1)+ is supported -- sharp at the one dimension where a
-- solution exists.
/-- info: 'CSD.SigmaLayer.orthogonal_preparation_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.orthogonal_preparation_vanishes

/-- info: 'CSD.SigmaLayer.vanishes_on_interval_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.vanishes_on_interval_of_dense

-- STEP THREE (2026-07-28): THE CAP IS NOW UNCONDITIONAL AT N >= 3
-- (SigmaLayer/ContextFixedA7FS.lean). Step two left the cap conditional on an ABUNDANCE
-- hypothesis -- that two overlap coordinates can jointly take values in any positive-measure set
-- below 1/2. fs_joint_abundance DISCHARGES it for the actual Fubini-Study measure, via the
-- corpus's own pushforward fs_volume_eq_dirichlet_inter (mu_FS pushes to the UNIFORM/Dirichlet
-- measure on the open simplex). Abundance then reduces to Lebesgue positivity on Fin M -> R, with
-- an EXPLICIT witness: the two chosen coordinates in T, every other coordinate in a small (0, eps).
-- The one subtlety is that T subset (0,1/2) bounds t_j + t_k < 1 POINTWISE BUT NOT UNIFORMLY, so
-- exists_trunc_of_volume_pos first passes to a positive-measure part of T bounded away from 1/2 --
-- only then is there uniform room for the remaining coordinates.
-- ★ fs_cap_unconditional: a base-only, U(N)-covariant, NONNEGATIVE preparation density reproducing
-- Born on the Fubini-Study sector VANISHES A.E. ON OVERLAP VALUES BELOW 1/2, with no hypothesis
-- left over. Sharp and attained -- the N=2 density 4(2s-1)+ is supported exactly on (1/2, 1].
-- ★ WHY N >= 3 IS EXACTLY THE THRESHOLD: M = N-1 is the number of free simplex coordinates, and
-- two DISTINCT ones exist precisely when M >= 2. At N=2 there is one free coordinate and the second
-- Born weight is 1 - s_1 -- functionally dependent (ContextFixedA7.joint_degenerate_of_sum_eq_one).
-- So the dimension count that powers this file is the same one that exempts the qubit.
-- This replaces the NUMERICAL evidence the retracted "provably dead" row rested on with a DERIVED
-- constraint. Still not the no-go: generic-psi and the harmonic argument remain open.
/-- info: 'CSD.SigmaLayer.exists_trunc_of_volume_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.exists_trunc_of_volume_pos

/-- info: 'CSD.SigmaLayer.volume_inter_openSimplexFree_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.volume_inter_openSimplexFree_pos

/-- info: 'CSD.SigmaLayer.fs_joint_abundance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.fs_joint_abundance

/-- info: 'CSD.SigmaLayer.fs_cap_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.SigmaLayer.fs_cap_unconditional

-- Hong-Ou-Mandel CSD twin (2026-07-27): the dip as an ONTIC IMPOSSIBILITY, not a statistical
-- cancellation. hom_coincidence_typicality_zero -- the coincidence cell's fibre typicality is
-- EXACTLY 0, so the set of microstates yielding a coincidence is NULL; there is nothing in Sigma
-- to cancel. Same at the record level (hom_coincidence_record_null: the P5 record event "recorded
-- a coincidence" is a null subset of Sigma) and as a Measurement (hom_coincidence_measurement_zero).
-- hom_bunch_typicality_half confirms the weight went to the two bunched outcomes (1/2 each), so
-- the vanishing is a genuine redistribution rather than a normalisation artefact. The occupation
-- state is DERIVED from the QM module (homOut_eq_bsTwo_bosonIn: |20>/|02> are the diagonal entries
-- of bsTwo bosonIn and the |11> amplitude is the symmetrised off-diagonal (S01+S10)/sqrt2), not
-- re-asserted. ARCHITECTURAL NOTE: this twin uses the RECORD LAYER, not the Duistermaat-Heckman
-- fs_born_volume_ratio_N / fsMeasure_bornRegionN route that every earlier ...Volume twin uses --
-- because those carry hpos (STRICTLY POSITIVE Born weights) and HOM's defining feature is a ZERO
-- amplitude. hpos is load-bearing there, not decorative: replaceMap_det b i = b i (Cramer), so a
-- zero weight makes the vertex-replacement map SINGULAR, puts b on the simplex boundary
-- (b in openSimplexFree fails) and breaks both the openness/measurability and volume-scaling steps.
-- volume_cdfCell has NO positivity hypothesis (a zero rate is just a zero-width cell), so the
-- record layer expresses the degenerate case the projective machinery cannot. Extending the DH
-- lemmas to the simplex boundary is an open item (specs/BACKLOG.md).
/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_typicality_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_typicality_zero

/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_record_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_record_null

/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_measurement_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_coincidence_measurement_zero

/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_bunch_typicality_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.hom_bunch_typicality_half

/-- info: 'CSD.Empirical.CSDBridge.HongOuMandelVolume.homOut_eq_bsTwo_bosonIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.HongOuMandelVolume.homOut_eq_bsTwo_bosonIn

-- CSD Volume twins (Born = Kähler typicality volume, 2026-07-27): LG survival cos²Δ and EV split 1/2
-- realised as Fubini–Study moment-sublevel volumes on ℂℙ¹ via fs_born_volume_ratio_qubit_uncond (DH).
/-- info: 'CSD.Empirical.CSDBridge.LeggettGargVolume.lg_survival_as_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.LeggettGargVolume.lg_survival_as_volume

/-- info: 'CSD.Empirical.CSDBridge.ElitzurVaidmanVolume.ev_split_as_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.ElitzurVaidmanVolume.ev_split_as_volume

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

-- Helstrom bound: minimum-error state discrimination (K3, Mathlib/QuantumInfo/Helstrom.lean).
-- The OPERATIONAL meaning of the trace distance, and the converse companion to
-- channel_traceDist_le above: channels cannot increase distinguishability, and the Helstrom
-- bound is exactly how much distinguishability a measurement can extract. Both halves are
-- pinned -- the bound (successProb_le, over every two-outcome test 0 ≤ E ≤ 1) AND its
-- ATTAINMENT (successProb_helstromTest, at the positive-eigenspace projector of the Helstrom
-- operator), so ½(1 + D) is the optimum, not merely an upper bound. Equal-prior form
-- errorProb_helstromTest: P_error = ½(1 − D(ρ₀,ρ₁)); general-prior form successProbPrior_le:
-- P_success ≤ ½(1 + ‖p₀ρ₀ − p₁ρ₁‖₁). Extremes: D = 0 forces a coin flip for EVERY E
-- (helstrom_indistinguishable), D = 1 permits an error-free test (helstrom_perfect).
-- Foundational triple, no `sorry`, no `native_decide`. Complements Empirical/QM/USD.lean
-- (zero error at the cost of an inconclusive outcome) -- the other end of the trade-off.
/-- info: 'QuantumInfo.re_trace_posPart_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.re_trace_posPart_eq

/-- info: 'QuantumInfo.re_trace_mul_le_helstrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.re_trace_mul_le_helstrom

/-- info: 'QuantumInfo.re_trace_mul_helstrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.re_trace_mul_helstrom

/-- info: 'QuantumInfo.helstromTest_isTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.helstromTest_isTest

/-- info: 'QuantumInfo.successProb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.successProb_le

/-- info: 'QuantumInfo.successProb_helstromTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.successProb_helstromTest

/-- info: 'QuantumInfo.errorProb_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.errorProb_ge

/-- info: 'QuantumInfo.errorProb_helstromTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.errorProb_helstromTest

/-- info: 'QuantumInfo.helstrom_indistinguishable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.helstrom_indistinguishable

/-- info: 'QuantumInfo.helstrom_perfect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.helstrom_perfect

/-- info: 'QuantumInfo.successProbPrior_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.successProbPrior_le

/-- info: 'QuantumInfo.successProbPrior_helstromTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.successProbPrior_helstromTest

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

-- BB84 QKD security (Crypto/BB84.lean): intercept-resend QBER (¼ sifted-key error),
-- eavesdropping detectability (¼ > 0 baseline), and the non-orthogonality
-- disturbance root (⟨0|+⟩ = (√2)⁻¹ ≠ 0). All Born-grounded via ‖⟨a|b⟩‖²; the
-- intercept-resend error is a classical marginal over Eve's outcome (no collapse
-- operator). Full composable finite-key security stays out of scope (LF5 gate).
-- Foundational triple only.
/-- info: 'CSD.Empirical.BB84.bb84_qber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_qber

/-- info: 'CSD.Empirical.BB84.bb84_intercept_resend_wrong_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_intercept_resend_wrong_basis

/-- info: 'CSD.Empirical.BB84.bb84_intercept_resend_right_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_intercept_resend_right_basis

/-- info: 'CSD.Empirical.BB84.bb84_eavesdropping_detectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_eavesdropping_detectable

/-- info: 'CSD.Empirical.BB84.bb84_states_nonorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_states_nonorthogonal

/-- info: 'CSD.Empirical.BB84.bb84_no_eavesdrop_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bb84_no_eavesdrop_error_zero

/-- info: 'CSD.Empirical.BB84.bornProb_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bornProb_comm

/-- info: 'CSD.Empirical.BB84.bornProb_ket0_ket0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bornProb_ket0_ket0

/-- info: 'CSD.Empirical.BB84.bornProb_ket0_ket1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bornProb_ket0_ket1

/-- info: 'CSD.Empirical.BB84.bornProb_ket0_ketPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.BB84.bornProb_ket0_ketPlus

-- B92 QKD security (Crypto/B92.lean): the two-state protocol. Unambiguous-
-- discrimination structure (error-free conclusive events ⟨1|0⟩=⟨−|+⟩=0 + ½
-- conclusive rates) and the no-cloning security root (no universal cloner copies
-- both encoding states |0⟩, |+⟩). All Born-grounded via ‖⟨a|b⟩‖², reusing BB84's
-- Born layer. Full composable finite-key security stays out of scope (LF5 gate).
-- Foundational triple only.
/-- info: 'CSD.Empirical.B92.b92_no_perfect_eavesdrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_no_perfect_eavesdrop

/-- info: 'CSD.Empirical.B92.b92_nonorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_nonorthogonal

/-- info: 'CSD.Empirical.B92.b92_unambiguous_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_unambiguous_one

/-- info: 'CSD.Empirical.B92.b92_unambiguous_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_unambiguous_zero

/-- info: 'CSD.Empirical.B92.b92_conclusive_rate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_conclusive_rate_one

/-- info: 'CSD.Empirical.B92.b92_conclusive_rate_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_conclusive_rate_zero

/-- info: 'CSD.Empirical.B92.b92_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.B92.b92_encode

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

-- Error discretization (2026-07-27): WHY correcting four Paulis corrects a CONTINUUM of errors.
-- pauli_decomposition -- every 2x2 complex matrix is c0.I + c1.X + c2.Z + c3.XZ with the
-- coefficients read off its entries ((M00 +/- M11)/2, (M01 +/- M10)/2); no analysis, no choice.
-- pauli_span_top says the same as span C {I,X,Z,XZ} = TOP: the Pauli set does not merely happen to
-- cover the errors a given code faces, it EXHAUSTS the single-qubit operator space.
-- error_discretization_qubit_1/2/3 lift it to the three-qubit code (kron3 is C-linear in each
-- slot), and errored_codeword_eq lands it on states: an arbitrary single-qubit error produces
-- exactly the corresponding combination of the four discrete corrupted states, so no continuum of
-- OUTCOMES accompanies the continuum of ERRORS. This is the conceptual content that makes
-- ThreeQubit (bit flips) + PhaseFlip (phase flips) a general error-correction claim rather than
-- two special cases. HONEST SCOPE (see the module's "Scope" section): this is the DISCRETIZATION
-- half only. It is NOT a proof that the three-qubit code corrects arbitrary errors -- that code's
-- correctable set is {I,X1,X2,X3} and Z errors lie outside it. Completing the argument to "any
-- single-qubit error" needs the CONCATENATED Shor 9-qubit code (open, specs/BACKLOG.md, blocked on
-- 512-dimensional infrastructure); the syndrome-collapse half (error subspaces orthogonal, so
-- measurement projects onto one correctable branch) is not claimed by THESE pins -- it is
-- delivered and pinned below (errored_pairwise_orthogonal, three_qubit_corrects_span_error).
/-- info: 'CSD.Empirical.QM.QEC.pauli_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.pauli_decomposition

/-- info: 'CSD.Empirical.QM.QEC.pauli_span_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.pauli_span_top

/-- info: 'CSD.Empirical.QM.QEC.error_discretization_qubit₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.error_discretization_qubit₁

/-- info: 'CSD.Empirical.QM.QEC.error_discretization_qubit₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.error_discretization_qubit₂

/-- info: 'CSD.Empirical.QM.QEC.error_discretization_qubit₃' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.error_discretization_qubit₃

/-- info: 'CSD.Empirical.QM.QEC.errored_codeword_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.errored_codeword_eq

-- Syndrome collapse (2026-07-27): the half that JOINS error discretization to the four
-- point-checks. Before this, the corpus had "an arbitrary error is a combination of four"
-- (ErrorDiscretization) and "each of the four is corrected" (ThreeQubit) with NOTHING connecting
-- them -- a superposition of error branches is not obviously reducible to one branch, so
-- discretization was true but load-BEARING on nothing. errored_pairwise_orthogonal supplies the
-- missing fact: the four errored codewords are mutually orthogonal (their supports are disjoint --
-- {000,111}, {100,011}, {010,101}, {001,110} -- which is the concrete form of the distinct
-- (Z1Z2,Z2Z3) syndrome pairs; available directly, so no spectral theorem needed).
-- branch_overlap_X1/X2/X3 is the collapse step proper: the overlap of the corrupted codeword with
-- branch k is EXACTLY c_k times that branch's norm, so the syndrome measurement reads off one
-- coefficient and is blind to the other three. three_qubit_corrects_span_error bundles all four
-- ingredients (decomposition, orthogonality, extraction, branch-wise recovery): THE CODE CORRECTS
-- AN ARBITRARY ERROR IN span C {I,X1,X2,X3} -- a continuum, not four points.
-- SCOPE: still the BIT-FLIP span, the 3-qubit code's actual correctable set. Reaching all four
-- Paulis per qubit (so pauli_span_top applies and EVERY single-qubit error is corrected) needs the
-- concatenated Shor-9 code, open on 512-dimensional infrastructure (specs/BACKLOG.md). What closed
-- here is the gap WITHIN the 3-qubit story.
/-- info: 'CSD.Empirical.QM.QEC.errored_pairwise_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.errored_pairwise_orthogonal

/-- info: 'CSD.Empirical.QM.QEC.spanError_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.spanError_logical

/-- info: 'CSD.Empirical.QM.QEC.branch_overlap_X1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.branch_overlap_X1

/-- info: 'CSD.Empirical.QM.QEC.branch_overlap_X2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.branch_overlap_X2

/-- info: 'CSD.Empirical.QM.QEC.branch_overlap_X3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.branch_overlap_X3

/-- info: 'CSD.Empirical.QM.QEC.three_qubit_corrects_span_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_corrects_span_error

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

-- Mach-Zehnder interference (2026-07-19, roadmap B4, the last iconic missing phenomenon): single-photon
-- two-mode interferometer = qubit phase circuit H·D(φ)·H·|0⟩ (= ramseyVec, machine-checked
-- ramseyVec_eq_circuit). Fringe cos²(φ/2) reuses ramsey_fringe_volume (Born-as-volume). NEW content:
-- interferometric visibility = 1 for a pure single photon (bright P(0)=1, dark P(π)=0). Foundational triple.
/-- info: 'CSD.Empirical.CSDBridge.MachZehnder.mz_visibility_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MachZehnder.mz_visibility_one

-- Double-slit interference + Bohr complementarity (2026-07-19): coherent fringe reuses MZ (visibility 1),
-- NEW content = which-path complementarity — measuring the slit makes the interference coherence
-- (off-diagonal of the decohered reduced state) VANISH (decoherence_offdiagonal_vanish), collapsing the
-- fringe to the flat classical mixture (visibility 0). The physical heart of the double slit; the part MZ
-- does not carry. Built on the LF6-B decoherence stratum. Foundational triple.
/-- info: 'CSD.Empirical.CSDBridge.DoubleSlit.doubleslit_complementarity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.DoubleSlit.doubleslit_complementarity

-- §14 CONNECTED (2026-07-19): the transport-only SternGerlach module now re-exports the genuine ontic
-- derivation (sg_frequency_convergence) so its CSD reading cites the ontic substrate, not only QM transport.
/-- info: 'CSD.Empirical.CSDBridge.SternGerlach.csd_sg_ontic_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlach.csd_sg_ontic_frequency_convergence

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
-- discharges modulo the posited sector symmetry (SO-1); the measure-⟹-metric route is false
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

-- §13.2 CONCRETE gate discharge (2026-07-19): the three single-qubit gate realisability Props
-- (hadamard/phaseS/phaseT_realisable_for) DISCHARGED on cpSectorData. Each gate's action is a genuine
-- CSDUnitaryBundle whose U_isometry is derived from the gate ∈ U(2) (inner_toEuclideanLin_unitary),
-- modulo the posited CSD sector (SO-1). Type carries U + U_isometry + Context, not a Σ-flow (PLACEHOLDERS §7), so the Σ-flow-lift
-- reading is the open D1 gap. Converts 3 of the 9 claim-shaped gate placeholders (PLACEHOLDERS §1) to proved.
/-- info: 'CSD.LF4.hadamard_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hadamard_realisable_cpSector

/-- info: 'CSD.LF4.phaseS_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.phaseS_realisable_cpSector

/-- info: 'CSD.LF4.phaseT_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.phaseT_realisable_cpSector

-- §13.2 gate discharge COMPLETE (2026-07-19): the remaining six gate realisability Props discharged on
-- cpSectorData (2-qubit CNOT/SWAP/CZ, multi-qubit Toffoli/Fredkin, composite Bell-prep). All nine gate
-- placeholders (PLACEHOLDERS §1) now proved; same honest scope (modulo the posited CSD sector (SO-1); type carries U + U_isometry +
-- Context, not a Σ-flow — D1 gap). U_isometry derived from the gate ∈ U(N) (inner_toEuclideanLin_unitary).
/-- info: 'CSD.LF4.cnot_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cnot_realisable_cpSector

/-- info: 'CSD.LF4.swap_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.swap_realisable_cpSector

/-- info: 'CSD.LF4.cz_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cz_realisable_cpSector

/-- info: 'CSD.LF4.toffoli_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.toffoli_realisable_cpSector

/-- info: 'CSD.LF4.fredkin_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fredkin_realisable_cpSector

/-- info: 'CSD.LF4.bell_prep_realisable_cpSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bell_prep_realisable_cpSector

-- SL-3 (2026-07-10): the §13.2 ontic lift on the NON-TRIVIAL-FIBRE instance kSectorData
-- (π = pr₁ many-to-one, Σ = ℂℙ^{N-1}×T²), the cpSectorActionBundle analogue on the Kähler instance.
-- Part 1 (thread Φ): the sector flow Φ=kFlow descends along π to f_Φ=id on rays
-- (kSectorDataFlow_projectable), which is TransProbPreserving (kProjectedFlow_transProbPreserving)
-- and fed through Wigner realises the unitary branch (kProjectedFlow_unitary_or_antiunitary) —
-- honest but degenerate (ray flow trivial; dynamics live in the T² fibre). Part 2 (genuine, caveat
-- C-1): the sector U(N)-action carries the FS-isometry — kSectorActionBundle's U_isometry is a Wigner
-- OUTPUT (kSectorActionBundle_U_isometry), not a posit. Does NOT derive TPP from measure-preservation
-- (that is the §13.2 trap / open D1 gap); SO-1 untouched.
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
/-- info: 'CSD.LF4.unitaryFlowSetup_liouville_isProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_liouville_isProbability

-- IsKahlerSector DE-VACUUMED (2026-07-19, manifest link L1): no longer `True`. Every ℂℙ-based instance
-- supplies IsKahlerSector := IsFubiniStudyKahler N -- the pointwise Fubini-Study Kähler-compatibility
-- triple (J²=-1, ω=g∘J, g=ω∘J, ω a (1,1)-form, ω u (Ju)=‖u‖²), PROVED axiom-free
-- (fubiniStudy_pointwise_kahler_compatibility). Only the manifold residual (dω=0, top-power volume
-- identity) stays unformalizable. isFubiniStudyKahler is the discharge.
/-- info: 'CSD.LF4.isFubiniStudyKahler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.isFubiniStudyKahler

-- Move up the chain (2026-07-10): UPGRADE the IsLiouvilleKahlerVolume content from "μ is a
-- probability measure" (C5 core) to "μ is THE volume forced by the space + U(N)-symmetry"
-- (IsForcedKahlerVolume: prob + invariant + UNIQUE, via fubiniStudyMeasure_unique). So the Kähler
-- volume is an OUTCOME of Σ = ℂℙ^{N-1} and its symmetry, not posited: fubiniStudyMeasure IS the forced
-- volume, the unitaryFlowSetup sector volume IS it, and the many-to-one instance's ray-space volume
-- π_*(kMuL) IS it (kMuL = forced-FS ⊗ Haar). IsKahlerSector (the 2-form) stays Mathlib-blocked (KG-1);
-- FORWARD (takes G=U(N) as given, does not derive it — SO-1 untouched).
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
-- rather than being evolved by the flow (= C6/L7, the SO-1/D1 frontier).
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
-- Same honest gap as C4: trials sample kMuL, not evolved by the flow (L7/SO-1).
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
-- general-N manyToOneSetup_born_frequency. FORWARD delivery (consumes the sector); SO-1 untouched.
/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_schrodinger_form

/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_both_pillars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_both_pillars

-- Schrödinger pillar DERIVED (2026-07-19): the (A)-by-rfl form above is now backed by an exercised
-- C¹-Stone derivation on the REAL nonzero generator at general N. schrodingerUnitary_hasDerivAt
-- DISCHARGES the smoothness datum U' t = U t·(-iH); manyToOneSchrodingerSetup_schrodinger_derived
-- exhibits the skew generator A = -iH, that discharged datum, the Stone conclusion U t = exp(t•A)
-- (CSD.StoneC1.eq_exp_of_hasDeriv), and the pillar — no longer only the A = 0 witness.
/-- info: 'CSD.LF4.schrodingerUnitary_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.schrodingerUnitary_hasDerivAt

/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_schrodinger_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_schrodinger_derived

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

-- SO-1 onramp (TypicalityForcing.lean): WHERE the Fubini–Study typicality measure comes from.
-- (A) fubiniStudy_forced_by_symmetry — any U(N)-invariant probability measure on the sector
-- ℂℙ^{N-1} IS the Fubini–Study measure (restates the axiom-free fubiniStudyMeasure_unique as
-- the typicality-derivation: Born = FS-volume is DERIVED from the sector symmetry G = U(N),
-- not posited). (B) obsFlow_not_uniquely_ergodic — a single ontic flow does NOT force FS: it
-- has ≥2 distinct invariant probability measures (μFS and δ_{[e₀]} at a fixed basis ray).
-- so1_onramp conjoins them. HONEST: typicality is forced by the SYMMETRY, not any flow; residual
-- SO-1 primitive = G = U(N) itself, which reduces to D1 (G-from-CSD-dynamics, NOT done). SO-1 not
-- closed. (SO-1 = the CSD sector origin, distinct from Paper C A5 = projectability.)
-- Foundational-triple-only (no busch).
/-- info: 'CSD.LF4.fubiniStudy_forced_by_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fubiniStudy_forced_by_symmetry

/-- info: 'CSD.LF4.obsFlow_not_uniquely_ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_not_uniquely_ergodic

/-- info: 'CSD.LF4.so1_onramp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.so1_onramp

-- (B′) STRENGTHENING (TypicalityForcing.lean): the obstruction to unique ergodicity is GENERIC,
-- via a CONSERVED QUANTITY. map_withDensity_of_conserved — reweighting an invariant measure by a
-- conserved density (d ∘ T = d) keeps it invariant (the genuine conserved-quantity mechanism).
-- withDensity_momentMap_obsFlow_invariant — instantiated at the conserved Born coordinate
-- momentMap·i (momentMap_obsFlow): μFS.withDensity (g ∘ momentMap·i) is obsFlow-invariant.
-- obsFlow_continuum_invariant — a CONTINUUM (Set.InjOn on [0,1]) of pairwise-distinct
-- obsFlow-invariant PROBABILITY measures (convex-combo witness s·μFS+(1-s)·δ_{[e₀]}; the
-- conserved Born coordinates are the structural WHY). HONEST: strengthens the obstruction;
-- still does NOT force FS / NOT close SO-1. Foundational-triple-only (no busch).
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
-- so1_obstruction_capstone — packages (1)⇒(2): single flow ⇒ non-constant conserved observable
-- ⇒ not μFS-ergodic ⇒ cannot force μFS. HONEST: CLOSES the single-flow obstruction story; an
-- ergodic flow (only-constant conserved observables) is what D1 must supply; residue = G-from-D1.
-- SO-1 NOT closed. Foundational-triple-only (no busch).
/-- info: 'CSD.LF4.momentMap_obsFlow_nonconstant_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_obsFlow_nonconstant_conserved

/-- info: 'CSD.LF4.obsFlow_not_ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_not_ergodic

/-- info: 'CSD.LF4.so1_obstruction_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.so1_obstruction_capstone

-- D1c-2: the concrete BASE SectorData carrying a PHYSICALLY-MEANINGFUL Φ = obsFlow ≠ id
-- (the observable's Hamiltonian flow exp(i t Â) on the Fubini–Study Kähler base ℂℙ^{N-1}).
-- Strictly stronger than D1c-1's free T²-fibre translation (kSectorDataFlow): dynamics on
-- the actual projective state space, not a trivial fibre shift. obsFlow is a single
-- observable's periodic phase flow (not de-isolation Φ_vN, not ergodic); SO-1 ergodicity gap
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
-- Still foundational-triple; weights-from-flow (SO-1) untouched.
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

-- SL-2 (2026-07-09): the singlet preparation rebuilt over the Φ≠id sector kSectorDataFlow (Φ=kFlow),
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

-- LF4 §14 general-N discharge for DIAGONAL observables (2026-07-22): the Hilbert expectation of
-- diagonal(lam·) equals the eigenvalue-weighted sum of the ontic Born-region volumes, at all N and
-- all real eigenvalues. Foundational triple only; carving-free, Gleason-free.
/-- info: 'CSD.LF4.observable_correspondence_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.observable_correspondence_diagonal

-- LF4 §14 general-N diagonal observable, canonical INTEGRAL form (2026-07-22): ⟨ψ,Aψ⟩ = ∫ A_ontic dμ
-- with A_ontic = ∑ₖ lam k · 𝟙_{Rₖ} an explicit measurable Σ-function. Foundational triple only.
/-- info: 'CSD.LF4.observable_correspondence_diagonal_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.observable_correspondence_diagonal_integral

-- LF4 §14 GENERAL (non-diagonal) self-adjoint observable (2026-07-22): via spectral unitary transport
-- of the state (φ = Uᴴψ), ⟨ψ,Aψ⟩ = ∑ₖ λₖ·vol(bornRegionN φ k) = ∫ aOntic φ λ dμ. Foundational triple.
/-- info: 'CSD.LF4.hermitian_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_observable_correspondence

/-- info: 'CSD.LF4.hermitian_observable_correspondence_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_observable_correspondence_integral

-- LF4 §14 STATES obligation (pure states / rank-one projectors, 2026-07-23): ‖⟨Φ,ψ⟩‖² = an ontic
-- Fubini–Study volume, via a unitary sending e₀ ↦ Φ. Foundational triple only.
/-- info: 'CSD.LF4.pure_state_born_prob_eq_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pure_state_born_prob_eq_volume

-- LF4 §14 STATES obligation, MIXED-STATE / density-operator case (2026-07-23): Tr(ρ·|φ⟩⟨φ|) =
-- ρ-eigenvalue-weighted sum of ontic Fubini–Study volumes of ρ's pure eigenstates. Foundational triple.
/-- info: 'CSD.LF4.mixed_state_born_eq_ensemble_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.mixed_state_born_eq_ensemble_volume

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
-- LF2 operational Born derivation. Since `busch_effect_gleason` was discharged
-- (2026-07-21), it now stands on the foundational triple alone.
/-- info: 'CSD.LF4.ontic_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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
-- (SO-1). Foundational triple throughout; Gleason-free.
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
-- FS-volume engine; the CSD sector is posited (SO-1); decoherence/partial-trace NOT here (gated
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
-- class sum of pointer-block limits, tendsto_finsetSum); synOutcome is the
-- per-microstate syndrome outcome function (vnPointerOutcome.map synClass) whose
-- some-s fibre is the class-block union; the syndrome outcome event frequency
-- (a single event per syndrome) converges a.s. to syndromeWeight (union-indicator
-- split over the genuinely disjoint class cells via bornRegion_pairwiseDisjoint +
-- e injectivity). Projective / coherent-error tier; Born numbers reused; the CSD sector is posited (SO-1);
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
-- Residue SO-1 (entangled sector posited); LF6-A.2 (full ℂℙ¹⁵ de-isolation flow)
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
-- productPartition_ghz_nonvacuous: product partitions exist. Residue SO-1 (GHZ
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
-- measurement. Residue SO-1 (GHZ entangled sector posited). Foundational triple only, no busch.
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
-- single-qubit eigen-equation proved (tripartite eigen-eq is the tensor, definitional). Residue SO-1
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
-- factorisation Φ = Φ_A ⊗ Φ_B deferred to LF6-A.3. Residue SO-1 (entangled sector posited);
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
-- carve (A.2) and the entangled preparation (SO-1). Foundational triple only, no busch.
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
-- non-locality lives in the contextual carve (C.1/C.3) and the entangled preparation (SO-1).
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
-- FS-volume-drift geometry; purity/entropy. Residue SO-1 (FS-typicality posited).
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
-- environment growth. Residue SO-1 (FS-typicality posited).
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
-- DEFERRED: continuous-time Lindblad / environment growth. Residue SO-1 (FS-typicality posited).
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
-- realises not derives. Residue SO-1 (entangled sector posited). Foundational triple only, no busch, no
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
-- c=s=1/√2 it collapses to Φ⁺ (psQubit_pauli_correlation_maximal).
/-- info: 'CSD.LF6.psQubit_pauli_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.psQubit_pauli_correlation

/-- info: 'CSD.LF6.psQubit_pauli_correlation_maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.psQubit_pauli_correlation_maximal

-- LF6-6 residual DISCHARGED — Gisin's theorem (GisinTheorem.lean, 2026-07-19): the non-factorisation
-- witness for unequal Schmidt coefficients. Every pure entangled two-qubit state Ψ(c,s) (0<c,0<s,
-- c²+s²=1) violates CHSH: gisin_chsh_violation gives settings whose CHSH combination of the genuine
-- Hilbert-space expectations ⟨Ψ(c,s)|σ·a⊗σ·b|Ψ(c,s)⟩ exceeds 2. gisin_chsh_value: the closed form is
-- 2√(1+(2cs)²) (Horodecki optimum for T=diag(2cs,−2cs,1)); >2 since concurrence 2cs>0; =2√2 at c=s=1/√2.
/-- info: 'CSD.LF6.gisin_chsh_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.gisin_chsh_value

/-- info: 'CSD.LF6.gisin_chsh_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.gisin_chsh_violation

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

-- LF6-9 generator tier (LindbladGenerator.lean, 2026-07-20): the general Lindblad/GKSL generator
-- ℒ(ρ)=−i[H,ρ]+Σₖ(LₖρLₖ†−½{Lₖ†Lₖ,ρ}), previously undefined. lindbladGenerator_trace (trace annihilation
-- tr ℒ=0 ⟹ trace-preserving), lindbladGenerator_isHermitian (Hermiticity preservation), and
-- lindblad_dissipation_posSemidef (the jump part ΣₖLₖρLₖ† preserves PSD — the Choi/Kraus CP witness). The
-- dephasing instance: dephasingGenerator_eq_lindblad ((γ/2)(σzρσz−ρ) is GKSL with H=0, L=√(γ/2)σz) and
-- dephasingChannel_master_equation (the exhibited T2 channel solves d/dt Φ = ℒ_deph(Φ) — the Φ_t=e^{tℒ}
-- content). Foundational triple. Deferred: CP of e^{tℒ} for arbitrary generators (matrix-exp positivity).
/-- info: 'CSD.LF6.lindbladGenerator_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladGenerator_trace

/-- info: 'CSD.LF6.lindbladGenerator_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindbladGenerator_isHermitian

/-- info: 'CSD.LF6.lindblad_dissipation_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.lindblad_dissipation_posSemidef

/-- info: 'CSD.LF6.dephasingGenerator_eq_lindblad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dephasingGenerator_eq_lindblad

/-- info: 'CSD.LF6.dephasingChannel_master_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dephasingChannel_master_equation

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
-- flow realises not derives. Residue SO-1.
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
-- physical FS-typical preparation reading remains the LF1 typicality / sector posit (SO-1).
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

-- Continuity-only Stone (2026-07-23): differentiability derived (FTC + integral averaging), not assumed.
/-- info: 'CSD.StoneC1.stone_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.StoneC1.stone_continuous

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

-- SigmaLayer Tranche 1 (2026-07-12): the projective-sector foundation. ConstraintDynamics (deterministic
-- measure-preserving one-parameter-group ontic flow), RecordedFact/RecordSemantics/compatibleSet
-- (records as measurable contextual events; isolation = conditioning muL on the record history),
-- IsolationPreparation (LF1 adapter reusing prepMeasure), ProjectiveSector (measurable pi to CP^{N-1}, not
-- injective), and the Kähler adapters. No Born/unitarity/Fubini-Study as fields; those are uninhabited
-- theorem-target predicates (TheoremTargets). Foundational triple only.
/-- info: 'CSD.SigmaLayer.ConstraintDynamics.flow_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ConstraintDynamics.flow_bijective

/-- info: 'CSD.SigmaLayer.compatibleSet_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compatibleSet_measurable

/-- info: 'CSD.SigmaLayer.compatibleSet_append_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compatibleSet_append_singleton

/-- info: 'CSD.SigmaLayer.Preparation.conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.Preparation.conditionalMeasure_apply

/-- info: 'CSD.SigmaLayer.HistoryPreparation.conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.HistoryPreparation.conditionalMeasure_apply

/-- info: 'CSD.SigmaLayer.ProjectiveSector.projectiveLaw_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ProjectiveSector.projectiveLaw_apply

/-- info: 'CSD.SigmaLayer.kahlerProjectiveSector_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.kahlerProjectiveSector_pi

-- SigmaLayer Tranche 2 (2026-07-13): the de-isolation measurement layer + the concrete product forward
-- capstone. productSector_hasFubiniStudyPushforward proves bridge B1 (pi_*(muFS ⊗ vol) = muFS) for the
-- CP^{N-1}×T² product model; productProjectedFlow_hasHamiltonianRealisation inhabits target T5
-- (exp(-itH) realisation); product_projectiveSector_forward_capstone bundles measure preservation + projectability
-- + T5 + B1, no open hypotheses. DeisolationModel + establishedFact are the measurement/record interface.
/-- info: 'CSD.SigmaLayer.productSector_hasFubiniStudyPushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.productSector_hasFubiniStudyPushforward

/-- info: 'CSD.SigmaLayer.productProjectedFlow_hasHamiltonianRealisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.productProjectedFlow_hasHamiltonianRealisation

/-- info: 'CSD.SigmaLayer.product_projectiveSector_forward_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.product_projectiveSector_forward_capstone

/-- info: 'CSD.SigmaLayer.compatibleSet_appendEstablishedFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compatibleSet_appendEstablishedFact

-- SigmaLayer Tranche 2b (2026-07-13): the concrete de-isolation model from the LF5 pointer machinery.
-- vnDeisolationModel is a fully theorem-backed DeisolationModel on CP^{M} (M+1 = N*N): interaction =
-- measurementFlow (measure-preserving unitary), readout = vnPointerOutcome, outcome regions = pointer
-- fibres. vnDeisolationModel_records proves the readout records the established outcome (B5);
-- vnDeisolationModel_ae_total proves the outcome is established for a.e. initial ontic state (target T6),
-- by transferring bornOutcome_ae_isSome through the measure-preserving interaction.
/-- info: 'CSD.SigmaLayer.vnDeisolationModel_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.vnDeisolationModel_records

/-- info: 'CSD.SigmaLayer.vnDeisolationModel_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.vnDeisolationModel_ae_total

/-- info: 'CSD.SigmaLayer.lifted_projectiveSector_measurement_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.lifted_projectiveSector_measurement_capstone

-- SigmaLayer Tranche 2b Born statistics (2026-07-13): the concrete de-isolation model reproduces the Born
-- FREQUENCIES, not merely a defined outcome. vnDeisolationModel_born_frequency transfers the LF5
-- outcome-frequency capstone measurement_flow_outcome_frequency through the measure-preserving
-- interaction (composed trial process measurementFlow ∘ fsTrial), so the pointer-i readout frequency
-- converges a.s. to ‖⟨eᵢ,ψ⟩‖². lifted_projectiveSector_measurement_born_capstone bundles the full measurement:
-- measure preservation + unique outcome a.e. + record establishment + a.e. total + Born frequencies.
/-- info: 'CSD.SigmaLayer.vnDeisolationModel_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.vnDeisolationModel_born_frequency

/-- info: 'CSD.SigmaLayer.lifted_projectiveSector_measurement_born_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.lifted_projectiveSector_measurement_born_capstone

-- SigmaLayer Tranche 3 (2026-07-13): the composition/measurement targets (ledger T9-T15) as bridge interfaces
-- and uninhabited predicates (SigmaLayer/CompositeInterface.lean), inhabited by adapters wiring the existing
-- LF6/Empirical capstones (SigmaLayer/CompositeAdapters.lean). T15 no-signalling from the singlet marginals;
-- T14 Bell from the d-intrinsic CGLMP no-LHV force and the CHSH Tsirelson saturation; T13 contextuality
-- from Kochen-Specker (Cabello-18), Mermin-Peres and GHZ; T10 POVM normalisation. T9 (mixed states) left
-- out honestly: the ensemble/mixed-Born content is the reported Mathlib density-matrix gap.
/-- info: 'CSD.SigmaLayer.singlet_hasNoSignalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.singlet_hasNoSignalling

/-- info: 'CSD.SigmaLayer.maxEntangled_noLocalHiddenVariable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.maxEntangled_noLocalHiddenVariable

/-- info: 'CSD.SigmaLayer.singlet_hasTsirelsonSeparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.singlet_hasTsirelsonSeparation

/-- info: 'CSD.SigmaLayer.cabello18_noNonContextualValuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.cabello18_noNonContextualValuation

/-- info: 'CSD.SigmaLayer.merminPeres_noNonContextualValuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.merminPeres_noNonContextualValuation

/-- info: 'CSD.SigmaLayer.ghz_noNonContextualValuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ghz_noNonContextualValuation

/-- info: 'CSD.SigmaLayer.povm_weightsProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.povm_weightsProbability

-- SigmaLayer interference (T16) + tensor weave (2026-07-14). hadamardTest_hasBornInterference inhabits the
-- two-path Born-interference target from the Hadamard test ((1 + Re⟨ψ,Uψ⟩)/2); interference is a
-- consequence of the complex sector (P7) + Born rule (T1/T2), not a postulate. The tensor weave shows
-- the finite tensor product ℂ^{NA} ⊗ ℂ^{NB} = ℂ^{NA·NB} is DERIVED (tensorIndexEquiv on Fin NA × Fin NB,
-- the local algebra aliceOp_bobOp_commute, operator no-signalling tensorSector_no_signalling); only the
-- composite-is-tensor bridge (CompositeSector.tensor_dimension, B6) is posited (P3 parked).
/-- info: 'CSD.SigmaLayer.hadamardTest_hasBornInterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.hadamardTest_hasBornInterference

/-- info: 'CSD.SigmaLayer.aliceOp_bobOp_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.aliceOp_bobOp_commute

/-- info: 'CSD.SigmaLayer.tensorSector_no_signalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.tensorSector_no_signalling

-- SigmaLayer time-indexed records + persistence (2026-07-15, SL-T5 final follow-on): makes records physical.
-- flowedSemantics event ⟨c,i,t⟩ = Φ_t⁻¹'(region c i) genuinely uses the recorded time (the pointer
-- semantics ignored it). flowedSemantics_event_measure: μL(event ⟨c,i,t⟩) = μL(region c i) -- record
-- probability conserved under isolated evolution. flowedSemantics_event_flow: event ⟨c,i,t+s⟩ =
-- Φ_s⁻¹'(event ⟨c,i,t⟩) -- record covariant with the flow. flowedSemantics_persistence bundles both.
/-- info: 'CSD.SigmaLayer.flowedSemantics_event_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.flowedSemantics_event_measure

/-- info: 'CSD.SigmaLayer.flowedSemantics_event_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.flowedSemantics_event_flow

/-- info: 'CSD.SigmaLayer.flowedSemantics_persistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.flowedSemantics_persistence

-- SigmaLayer post-outcome preparation (2026-07-15, SL-T5 follow-on): closes the measurement/record loop.
-- HistoryPreparation.appendFact constructs the post-measurement preparation on the extended history
-- (history ++ [r]); its compatible region compatibleSet ∩ event r has PROVEN nonzero measure when the
-- outcome is possible. appendFactOfPos builds it from positive conditional probability
-- (conditionalMeasure(event r) ≠ 0). appendFact_conditionalMeasure_apply: the post-measurement law is
-- the Bayesian update μL(A ∩ (compatible ∩ event))/μL(compatible ∩ event).
/-- info: 'CSD.SigmaLayer.HistoryPreparation.appendFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.HistoryPreparation.appendFact

/-- info: 'CSD.SigmaLayer.HistoryPreparation.appendFact_conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.HistoryPreparation.appendFact_conditionalMeasure_apply

/-- info: 'CSD.SigmaLayer.HistoryPreparation.appendFactOfPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.HistoryPreparation.appendFactOfPos

-- SigmaLayer conditional->Luders correspondence (2026-07-15, SL-T5 follow-on): connects the two conditioning
-- rules the review flagged as unlinked. bayesianConditional w = w(fine)/w(coarse); BOTH the projective
-- Luders update (ludersUpdate_isBayesianConditional, over the Born weight) and the ontic record-history
-- conditioning (historyConditioning_isBayesianConditional, over the Liouville measure) are instances.
-- luders_record_conditioning_correspondence bundles both -- one conditioning rule, two weights. That the
-- two weights AGREE (asserted there, not proved) is now a THEOREM: ConditioningLuders.lean.
/-- info: 'CSD.SigmaLayer.luders_record_conditioning_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.luders_record_conditioning_correspondence

-- SigmaLayer conditioning->Luders WEIGHT AGREEMENT (2026-07-17, ConditioningLuders.lean): the missing link the
-- review flagged. onticRegion_measure_eq_born: μL(π⁻¹ bornRegion i) = ‖⟨eᵢ,ψ⟩‖² -- the ontic measure of the
-- i-th OUTCOME REGION equals the Born weight, via B1 (π_*μL=μFS) + Born-from-volume. So the ontic and Born
-- conditioning weights are the SAME number (previously only asserted). conditioning_born_ratio_correspondence:
-- the ontic Bayesian conditional of the outcome regions = the ratio of Born weights (probability-level
-- correspondence). Residual: all-effects operational STATE equivalence via projWeight.
/-- info: 'CSD.SigmaLayer.onticRegion_measure_eq_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.onticRegion_measure_eq_born

/-- info: 'CSD.SigmaLayer.conditioning_born_ratio_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conditioning_born_ratio_correspondence

-- SigmaLayer #4 OPERATIONAL EQUIVALENCE (2026-07-17, ConditioningLuders.lean): the review's #4 for pointer-basis
-- effects. projWeight_rankOne: projWeight(rank-1 proj eₖ)ψ = ‖⟨eₖ,ψ⟩‖² -- the formalism bridge between the
-- projWeight (E→ₗE) weight and the Born/region weight. onticWeight_eq_ludersWeight: μL(π⁻¹ bornRegion i) =
-- projWeight(rankOneProj i)ψ -- the ontic and Lüders conditioning weights are LITERALLY equal per outcome.
-- conditioning_luders_operational_equivalence: the two conditionings give the SAME conditional probability,
-- each in its native weight -- operational equivalence as PREDICTIONS, not measure=vector. Residual:
-- non-pointer-basis / general-projector effects (sums over ranges).
/-- info: 'CSD.SigmaLayer.projWeight_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.projWeight_rankOne

/-- info: 'CSD.SigmaLayer.onticWeight_eq_ludersWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.onticWeight_eq_ludersWeight

/-- info: 'CSD.SigmaLayer.conditioning_luders_operational_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conditioning_luders_operational_equivalence

-- SigmaLayer #4 GENERAL-EFFECT extension (2026-07-17, ConditioningLuders.lean): #4 completed for ALL pointer-basis
-- effects. onticRegion_biUnion_measure_eq_born_sum: μL(π⁻¹ ⋃_{k∈S} bornRegion k) = ∑_{k∈S} ‖⟨eₖ,ψ⟩‖² --
-- the weight agreement for an effect S (union of regions = sum of Born weights), via additivity over the
-- pairwise-disjoint Born regions. conditioning_luders_effect_equivalence: the ontic and Lüders conditionings
-- give the SAME conditional probability for every pointer-basis effect. So #4 (operational equivalence) is
-- proved for all diagonal effects on the product model.
/-- info: 'CSD.SigmaLayer.onticRegion_biUnion_measure_eq_born_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.onticRegion_biUnion_measure_eq_born_sum

/-- info: 'CSD.SigmaLayer.conditioning_luders_effect_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conditioning_luders_effect_equivalence

/-- info: 'CSD.SigmaLayer.ludersUpdate_isBayesianConditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ludersUpdate_isBayesianConditional

/-- info: 'CSD.SigmaLayer.historyConditioning_isBayesianConditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.historyConditioning_isBayesianConditional

-- SL-T5 unified many-to-one measurement capstone (2026-07-15): dynamics + measurement on ONE ontic
-- model. unified_projectiveSector_capstone puts BOTH the isolated Hamiltonian flow (productDynamics, exp(-itH)•)
-- AND the de-isolation measurement (measurementFlow on the base fibre) on the SAME (Σ=ℂℙ^{M}×T², μL=μFS⊗
-- vol, π=Prod.fst): flow measure-preserving + Schrödinger-projectable + FS pushforward + interaction
-- measure-preserving + a.e. readout (T6, lifted through π) + record establishment (B5). Removes the
-- forward-vs-measurement model split. unifiedDeisolationModel_ae_total lifts the base a.e. via Prod.fst.
/-- info: 'CSD.SigmaLayer.unified_projectiveSector_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unified_projectiveSector_capstone

-- SigmaLayer #5 TIME-INDEXED RECORDS ON THE UNIFIED MODEL (2026-07-17, UnifiedFlowedRecords.lean): the review's
-- #5. unifiedFlowedSemantics = flowedSemantics over the isolated flow productDynamics with the pointer-fibre
-- region; unified_records_persistence instantiates flowedSemantics_persistence ON the unified model (Born
-- weight conserved + flow-covariant under the exp(-itH) evolution); unifiedFlowedSemantics_zero: the static
-- vnRecordSemanticsProd is the t=0 slice (so the capstone is undisturbed). Records are now genuinely
-- time-physical ON the model -- the piece L9 needs to list records in "proved on the unified model".
/-- info: 'CSD.SigmaLayer.unified_records_persistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unified_records_persistence

/-- info: 'CSD.SigmaLayer.unifiedFlowedSemantics_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unifiedFlowedSemantics_zero

-- SigmaLayer #2 BORN-FREQUENCY ON THE UNIFIED MODEL (2026-07-17, UnifiedFlowedRecords.lean): the review's #2.
-- unified_born_frequency: for i.i.d. trials with the unified model's OWN law (productDynamics.muL), the
-- frequency of trials in π⁻¹(bornRegion i) converges a.s. to ‖⟨eᵢ,ψ⟩‖² -- a direct transfer of
-- manyToOneSetup_born_frequency through productDynamics.muL = liouvilleMeasure (rfl). Born frequencies now
-- stated ON the unified model itself, alongside dynamics/measurement/records/conditioning=Lüders.
/-- info: 'CSD.SigmaLayer.unified_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unified_born_frequency

-- FiniteQMClosure (#6, 2026-07-17): the tiered capstone. unifiedFiniteQMClosure bundles the eleven
-- GENUINELY-PROVED-on-the-unified-model facts (isolated flow measure-preserving, Schrödinger projection,
-- Fubini-Study bridge/B1, measurement preserving, readout a.e. total/T6, records established/B5, records
-- time-physical/#5, Born frequency/#2, conditioning=Lüders/#3#4) into one record, each field discharged by
-- its source lemma. The Choice-A posit, QM adapters, and open residue are documented in the module header,
-- not encoded as fields -- so no field is sorry and the tiers are honest.
/-- info: 'CSD.SigmaLayer.unifiedFiniteQMClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unifiedFiniteQMClosure

/-- info: 'CSD.SigmaLayer.unifiedDeisolationModel_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unifiedDeisolationModel_ae_total

-- SigmaLayer P3 SOLVED via local tomography (2026-07-15): composite_is_tensor_product. The composite observable
-- algebra IS the tensor product of the local ones -- compositeTensorEquiv (= kroneckerLinearEquiv) is a
-- SUFFICIENCY (2026-07-17 downgrade): BIJECTIVE linear iso M_{NA} ⊗ M_{NB} ≃ M_{NA·NB} sending
-- U ⊗ₜ Q ↦ aliceOp U · bobOp Q -- the standard tensor model REALIZES locality (commuting) + local tomography
-- (joint_mem_span_local). This is SUFFICIENCY, not uniqueness; the NECESSITY half (any composite with
-- commuting, generating local algebras IS the tensor product) is TensorReconstruction.lean below.
/-- info: 'CSD.SigmaLayer.composite_is_tensor_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.composite_is_tensor_product

-- SigmaLayer P3 RECONSTRUCTION (2026-07-17, TensorReconstruction.lean): the NECESSITY/uniqueness half.
-- compositeAlgReconstruction: commuting local embeddings M_m, M_n whose images GENERATE 𝒜 give an ALGEBRA
-- EQUIVALENCE M_m ⊗ M_n ≃ₐ 𝒜 (injective since M_m⊗M_n is SIMPLE -- matrixTensor_isSimpleRing; surjective
-- from generation). composite_dim_eq: for 𝒜 = M_k, forces k = m·n -- discharging bridge B6
-- (CompositeSector.tensor_dimension) as a THEOREM. So locality + generation FORCE ⊗, not just admit it.
/-- info: 'CSD.SigmaLayer.compositeAlgReconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compositeAlgReconstruction

/-- info: 'CSD.SigmaLayer.composite_dim_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.composite_dim_eq

-- SigmaLayer P3 BRIDGE B6 DISCHARGED (2026-07-17): CompositeSector.ofReconstruction builds a CompositeSector
-- whose tensor_dimension (NA*NB=Njoint) FIELD is filled by composite_dim_eq -- derived from commuting,
-- generating local embeddings, not posited. So B6 is no longer a bare assumption.
/-- info: 'CSD.SigmaLayer.CompositeSector.ofReconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.CompositeSector.ofReconstruction

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

-- CONSTPROP is a sound REDUCING optimization (cost side, 2026-07-18): the value-exact lever, now proved
-- BENEFICIAL. cprop_toffoli_le: the pass never increases the emitted Toffoli count ((circuitCost (cprop α c))
-- .toffoli ≤ (circuitCost c).toffoli) -- so with cprop_denote it is a valid Toffoli-reducing optimization.
-- foldGate_ccx_known_false: a non-degenerate CCX with a control known false folds AWAY (to []) -- where the
-- reduction is bought. andCell_constprop_reduces: the AND-adder carry cell [CCX a b g, CCX a c g, CCX b c g]
-- with carry-in known 0 constant-propagates 3 Toffoli -> 1, a value-exact 67% reduction on a real gadget.
/-- info: 'Reversible.cprop_toffoli_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.cprop_toffoli_le

/-- info: 'Reversible.foldGate_ccx_known_false' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.foldGate_ccx_known_false

/-- info: 'Reversible.andCell_constprop_reduces' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.andCell_constprop_reduces

/-- info: 'CSD.SigmaLayer.compositeTensorEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.compositeTensorEquiv_apply

-- SigmaLayer P3 resolution + localized sector posit (SO-1) (2026-07-15): reducing the two deep posits.
-- P3 (why tensor): single_prod (the joint basis matrix = product of local ones) + joint_mem_span_local
-- (the commuting local subalgebras GENERATE the whole joint algebra) -- the tensor product carries no
-- observables beyond local ones and their products, so B6 reduces from "posit ⊗" to "posit two full
-- local algebras that act and commute". SO-1 (sector origin) LOCALIZED: forcedVolume_unique /
-- region_measure_symmetry_forced (any two U(N)-invariant measures give the same region weights, so the
-- Born weights are symmetry-forced, not measure-chosen); localised_sectorPostulate_capstone (the concrete sector's
-- typicality is forced by the U(N) symmetry the flow is part of -- "the sector posit in the appropriate places (SO-1)").
-- Neither closes the universal posit (P3 "why ⊗" / sector-origin-from-bare-flow (SO-1)); both reduce where it bites.
/-- info: 'CSD.SigmaLayer.single_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.single_prod

/-- info: 'CSD.SigmaLayer.joint_mem_span_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.joint_mem_span_local

/-- info: 'CSD.SigmaLayer.region_measure_symmetry_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.region_measure_symmetry_forced

/-- info: 'CSD.SigmaLayer.localised_sectorPostulate_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.localised_sectorPostulate_capstone

-- SigmaLayer SO-1 NO-GO (2026-07-15): the single-flow limit made a PROVED boundary. A projective unitary flow with
-- two distinct fixed rays admits an invariant probability measure /= mu_FS (the two fixed-ray Diracs), so a
-- single deterministic flow does NOT pin the sector's typicality measure -- "the CSD sector is posited (SO-1)" is a theorem
-- about the limit, not a formalisation gap. phaseFlip_admits_invariant_ne_fubiniStudy exhibits it on the
-- concrete nontrivial flow diag(1,-1) on CP^1. Positive companion: region_measure_symmetry_forced (full U(N)
-- symmetry DOES pin mu_FS). Matches Paper C (S1.4): Sigma, pi, the A5 sector are assumed, not derived.
/-- info: 'CSD.SigmaLayer.flow_admits_invariant_ne_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.flow_admits_invariant_ne_fubiniStudy

/-- info: 'CSD.SigmaLayer.phaseFlip_admits_invariant_ne_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.phaseFlip_admits_invariant_ne_fubiniStudy

-- UniqueErgodicity (2026-07-19, SO-1/L7 ergodic face sharpened): UniquelyErgodic defined (absent from
-- Mathlib) + UniquelyErgodic ⇒ Ergodic (via Ergodic.of_mem_extremePoints: singleton invariant-measure
-- set) + the scaffold link Ergodic(Φ_1) ⇒ IsErgodicForOutcomeRegions. Does NOT prove BornFromFlow
-- (needs the Mathlib-absent pointwise Birkhoff theorem); the unitary no-gos above provably exclude the
-- hypothesis for the current flows (candidate must be non-unitary). Boundary-marking, not SO-1 closure.
/-- info: 'CSD.SigmaLayer.UniquelyErgodic.ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.UniquelyErgodic.ergodic

/-- info: 'CSD.SigmaLayer.isErgodicForOutcomeRegions_of_uniquelyErgodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.isErgodicForOutcomeRegions_of_uniquelyErgodic

-- SigmaLayer Bell/contextuality generality (2026-07-14): the UNIVERSAL bounds behind the per-instance T13/T14
-- witnesses. lhv_chsh_le_two (every LHV: |S| ≤ 2), qm_chsh_le_tsirelson (every state: |S| ≤ 2√2),
-- cglmp_lhv_le_two (every LHV table, every d: cglmp ≤ 2), bell_general_separation (2 < 2√2, gap attained
-- by the singlet), general_ks_noNonContextualValuation (any parity-(18,9) config, not just Cabello-18).
/-- info: 'CSD.SigmaLayer.lhv_chsh_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.lhv_chsh_le_two

/-- info: 'CSD.SigmaLayer.qm_chsh_le_tsirelson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.qm_chsh_le_tsirelson

/-- info: 'CSD.SigmaLayer.bell_general_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.bell_general_separation

/-- info: 'CSD.SigmaLayer.general_ks_noNonContextualValuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.general_ks_noNonContextualValuation

-- SigmaLayer T8: the projective (Lüders) update (2026-07-14). luders_capstone bundles the three defining
-- properties of the projective post-measurement update ludersUpdate p x = (‖p x‖)⁻¹ • p x: normalised,
-- repeatable (p fixes it, so re-measurement is certain), and Lüders = conditional probability
-- (ludersUpdate_conditional: the updated Born weight of a finer projection q is projWeight q x /
-- projWeight p x). projWeight_eq_re_inner ties the weight ‖p x‖² to the effect form Re⟨x, p x⟩;
-- isProjection_toEuclideanLin connects matrix projectors. Closes the T8 gap left by MeasurementRecord.
/-- info: 'CSD.SigmaLayer.luders_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.luders_capstone

/-- info: 'CSD.SigmaLayer.ludersUpdate_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ludersUpdate_conditional

/-- info: 'CSD.SigmaLayer.projWeight_eq_re_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.projWeight_eq_re_inner

-- SigmaLayer T7: the general (non-projective) conditional state update (2026-07-14). conditionalUpdate_capstone
-- bundles the general Kraus/effect update stateUpdate M x = (‖M x‖)⁻¹ • M x for a measurement operator M
-- (effect E = M† M): normalised, outcome weight = Re⟨x, M† M x⟩ (updateWeight_eq_re_inner), and the
-- sequential (Wigner) rule stateUpdate_sequential (updateWeight N (stateUpdate M x) = updateWeight N
-- (M x) / updateWeight M x). Lüders (T8) is the sharp special case (stateUpdate_eq_ludersUpdate); T7
-- needs neither self-adjointness nor idempotence.
/-- info: 'CSD.SigmaLayer.conditionalUpdate_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conditionalUpdate_capstone

/-- info: 'CSD.SigmaLayer.stateUpdate_sequential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.stateUpdate_sequential

/-- info: 'CSD.SigmaLayer.stateUpdate_eq_ludersUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.stateUpdate_eq_ludersUpdate

-- SigmaLayer T9: the mixed-state representation (2026-07-14). Closes the density-matrix gap on the statistical
-- side. mixedState_capstone / traceForm_mix: the convex mixture mix p ρ₁ ρ₂ is a density operator and
-- the Born rule traceForm is affine in the state (Tr((p ρ₁ + (1-p) ρ₂) E) = p Tr(ρ₁ E) + (1-p) Tr(ρ₂ E)).
-- rankOneDensity_isPure: pure states are the rank-one projectors; maximallyMixed_not_isPure: I/N is a
-- genuinely mixed state for N ≥ 2 (non-vacuity). Built on LF2.DensityOperator/Effect/traceForm; the
-- purity converse Tr(ρ²)=1 → ρ²=ρ (spectral theorem) is left as a residue.
/-- info: 'CSD.SigmaLayer.mixedState_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.mixedState_capstone

/-- info: 'CSD.SigmaLayer.traceForm_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.traceForm_mix

/-- info: 'CSD.SigmaLayer.maximallyMixed_not_isPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.maximallyMixed_not_isPure

-- T9 purity converse (2026-07-14): the spectral-theorem direction, closing the residue. IsPure ρ ↔
-- Tr(ρ²)=1 (isPure_iff_trace_sq_one); the converse isPure_of_trace_sq_one uses Matrix spectral theory
-- (∑λᵢ = ∑λᵢ² = 1, λᵢ ≥ 0 ⇒ λᵢ ∈ {0,1} ⇒ ρ² = ρ). Foundational triple.
/-- info: 'CSD.SigmaLayer.isPure_of_trace_sq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.isPure_of_trace_sq_one

/-- info: 'CSD.SigmaLayer.isPure_iff_trace_sq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.isPure_iff_trace_sq_one

-- MixedEnsemble (#8 A+B, 2026-07-17): the mixed-state / ensemble representation. A -- finite ensembles:
-- ensemble w ρ = ∑ᵢ wᵢρᵢ (∑wᵢ=1, wᵢ≥0) is a density operator via posSemidef_sum; traceForm_ensemble is
-- the affine Born rule over the whole ensemble, Tr((∑wᵢρᵢ)E) = ∑wᵢTr(ρᵢE) (the many-component
-- traceForm_mix). B -- spectral ensemble decomposition: density_eq_eigen_ensemble (ρ = ∑λᵢ|eᵢ⟩⟨eᵢ| via
-- the Hermitian spectral theorem), eigenvalues_isProbability (λ a probability distribution),
-- density_isPureEnsemble (every density operator IS a convex ensemble of pure states), and
-- traceForm_eq_pureEnsemble / mixedEnsemble_capstone (the Born rule of a mixed state is the
-- eigenvalue-weighted average of the pure Born rules).
/-- info: 'CSD.SigmaLayer.ensemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.ensemble

/-- info: 'CSD.SigmaLayer.traceForm_ensemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.traceForm_ensemble

/-- info: 'CSD.SigmaLayer.density_eq_eigen_ensemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.density_eq_eigen_ensemble

/-- info: 'CSD.SigmaLayer.density_isPureEnsemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.density_isPureEnsemble

/-- info: 'CSD.SigmaLayer.mixedEnsemble_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.mixedEnsemble_capstone

-- Mixed-Born on the COMPOSITE INDEXED density type (2026-07-19, SL-T3 T9 residual closed): the
-- MixedEnsemble content (affine Born + spectral ensemble) ported from DensityOperator (Fin N) to
-- DensityOperatorIx ι (arbitrary Fintype index — the type the bipartite/composite interface uses via
-- reduced/reducedLeft). traceForm_ensemble = affine; mixedEnsemble_capstone = Born is the
-- eigenvalue-weighted avg of pure Born rules, on the indexed type. Closes the reported density-matrix gap.
/-- info: 'CSD.LF2.DensityOperatorIx.traceForm_ensemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.DensityOperatorIx.traceForm_ensemble

/-- info: 'CSD.LF2.DensityOperatorIx.mixedEnsemble_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF2.DensityOperatorIx.mixedEnsemble_capstone

-- MixedOntic (#8 C, 2026-07-17): the ontic-side mixed-state representation on the unified model.
-- mixed_ontic_born_weight: for any density operator ρ and pointer outcome i, the classical mixture over
-- ρ's spectral ensemble (λⱼ,eⱼ) of the ontic Born-region measures ∑ⱼ λⱼ·μL(π⁻¹ bornRegion(eⱼ) i) equals
-- Tr(ρ Eᵢ) = traceForm ρ (rankOneEffect eᵢ) -- composing onticRegion_measure_eq_born with
-- traceForm_eq_pureEnsemble + born_quadratic. So productDynamics represents mixed states, not only pure ψ;
-- wired as the FiniteQMClosure.mixed_born field. Weight-level (the mixed frequency LLN is the refinement).
/-- info: 'CSD.SigmaLayer.mixed_ontic_born_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.mixed_ontic_born_weight

-- MixedFrequency (#8 C, a.s. limit, 2026-07-19, roadmap A1): the mixed Born WEIGHT upgraded to a
-- FREQUENCY LLN. unified_mixed_born_frequency: for i.i.d. two-stage trials Y whose law is mixtureMeasure
-- (eigenvalue distribution ⊗ μL), the frequency in mixtureRegion i (component j's eigenvector lands in the
-- i-th ontic Born region) converges a.s. to Tr(ρ Eᵢ). Proof: mixtureMeasure_region_toReal shows the
-- two-stage region measure = Tr(ρ Eᵢ) (via Measure.prod_prod + eigenvalueMeasure_singleton +
-- mixed_ontic_born_weight), then born_frequency_convergence_partition. Wired as FiniteQMClosure's 11th
-- field mixed_born_frequency, closing the closure's last open QM item (Tier-4 mixed frequency LLN).
/-- info: 'CSD.SigmaLayer.unified_mixed_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.unified_mixed_born_frequency

/-- info: 'CSD.SigmaLayer.mixtureMeasure_region_toReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.mixtureMeasure_region_toReal

-- Symmetrization (identical particles / exchange statistics, n=2, 2026-07-18): the swap operator on
-- H⊗H = EuclideanSpace ℂ (Fin N × Fin N) is a self-adjoint involution (swap_isSymmetric); symProj/
-- antisymProj = ½(1±swap) are complementary orthogonal projections (symProj_idem, symProj_antisymProj,
-- symProj_add_antisymProj); the exchange dichotomy Sym=(+1)/Anti=(-1) eigenspaces (swap_eq_self_iff,
-- swap_eq_neg_iff, eq_zero_of_swap_self_and_neg → H⊗H = Sym⊕Anti); and Pauli exclusion
-- antisymProj_tprod_self (antisymProj (v⊗v) = 0: no two fermions in the same state).
/-- info: 'CSD.SigmaLayer.swap_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.swap_isSymmetric

/-- info: 'CSD.SigmaLayer.symProj_add_antisymProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.symProj_add_antisymProj

/-- info: 'CSD.SigmaLayer.swap_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.swap_eq_self_iff

/-- info: 'CSD.SigmaLayer.swap_eq_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.swap_eq_neg_iff

/-- info: 'CSD.SigmaLayer.antisymProj_tprod_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.antisymProj_tprod_self

-- OnticBornFrequency (connectivity G1, 2026-07-25): Born grounded in the ONTIC typicality. The only
-- hypothesis is ontic (trials sample μ_L = D.muL, the floor); the epistemic μ_FS and Born are DERIVED.
-- onticBornVolume_eq: Born = the ontic typicality volume — μ_L(π⁻¹ bornRegion) = ‖⟨eᵢ,ψ⟩‖² via the
-- pushforward bridge (HasFubiniStudyPushforward) + bornRegion_fs_measure_uncond, for ANY sector.
-- born_frequency_from_ontic_sampling: iid ontic-μ_L trials → Born frequency (freq_tendsto_of_iid).
-- productModel_onticBornVolume: non-vacuity — hpush discharged by the proved productSector pushforward.
/-- info: 'CSD.SigmaLayer.onticBornVolume_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.onticBornVolume_eq

/-- info: 'CSD.SigmaLayer.born_frequency_from_ontic_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.born_frequency_from_ontic_sampling

/-- info: 'CSD.SigmaLayer.productModel_onticBornVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.productModel_onticBornVolume

-- BornFibrePartition (record layer / MD-1, 2026-07-25): the fibre-partition factor of measurement.
-- The fibre F=ℝ is carved into cumulative (CDF) cells cdfCell whose Lebesgue measure equals a given
-- rate rᵢ (volume_cdfCell); the cells are pairwise disjoint (cdfCell_pairwiseDisjoint) so the fibre
-- is genuinely partitioned. Fed the Born rates rᵢ=‖ψ i‖²=|⟨eᵢ,ψ⟩|² (bornRate) the fibre measure of
-- outcome i is the Born weight (volume_bornCell), and for a unit state the cells cover a set of
-- measure exactly 1 (volume_iUnion_bornCell_unit) — the record-layer measure content. The open piece
-- is the dynamical realisation (a de-isolation flow with moment-map target-measures), not this.
/-- info: 'CSD.RecordLayer.volume_cdfCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.volume_cdfCell

/-- info: 'CSD.RecordLayer.cdfCell_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.cdfCell_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.volume_bornCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.volume_bornCell

/-- info: 'CSD.RecordLayer.volume_iUnion_bornCell_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.volume_iUnion_bornCell_unit

-- DeIsolationFlow (record layer / MD-1 step 2b′, 2026-07-25): the de-isolation outcome DISTRIBUTION.
-- On the canonical fibre typicality measure fibreTypicality = vol|[0,1) (a probability measure), the
-- Born cell i has fibre typicality exactly ‖ψ i‖² (fibreTypicality_bornCell = the outcome
-- probability), the cells cover the fibre up to a null set (fibreTypicality_uncovered = pointer a.e.
-- defined), and the abstract bridge map_pointer_apply shows ANY measurable pointer whose basins carry
-- the Born cell measures pushes fibreTypicality forward to the Born distribution. The open piece is
-- exhibiting such a pointer from a physical de-isolation Hamiltonian H_int(M) — the bridge's hbasin
-- hypothesis IS that obligation, not this theorem.
/-- info: 'CSD.RecordLayer.fibreTypicality_bornCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreTypicality_bornCell

/-- info: 'CSD.RecordLayer.fibreTypicality_uncovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreTypicality_uncovered

/-- info: 'CSD.RecordLayer.map_pointer_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.map_pointer_apply

-- FibreRecord (record layer / MD-1 step 3, 2026-07-25): the record-layer readout as a first-class
-- postulate-P5 RecordSemantics on Σ=ℝ. fibreRecordSemantics: record event of "context c recorded
-- outcome i" = cdfCell c.rate i, measurable + exclusive (distinct outcomes disjoint, from
-- cdfCell_pairwiseDisjoint). fibreOutcome_eq_record: the ontic selection fibreOutcome IS the record
-- (some i ↔ ξ in event). compatibleSet_fibre_single: isolation on one record = conditioning on the
-- cell. fibreTypicality_bornRecord: the ontic typicality of recording outcome i is exactly ‖ψ i‖²
-- (Born meets the record). The intended replacement for the prep-indexed LF5 vnPointerOutcome readout.
/-- info: 'CSD.RecordLayer.fibreRecordSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreRecordSemantics

/-- info: 'CSD.RecordLayer.fibreOutcome_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreOutcome_eq_record

/-- info: 'CSD.RecordLayer.fibreTypicality_bornRecord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fibreTypicality_bornRecord

-- RecordLayerClosure (record layer / MD-1 step 5, 2026-07-25): the record-layer capstone bundle, the
-- analog of FiniteQMClosure. recordLayerClosure discharges, for every unit ψ: exclusive (P5), the
-- ontic selection IS the record, isolation = conditioning on the cell (P6), born_typicality (fibre
-- typicality of the record event = ‖ψ i‖²), and ae_total (events cover the fibre up to null). The
-- certified successor to the prep-indexed vnPointerOutcome readout — outcome probabilities are
-- measurement-noncontextual. Migrating FiniteQMClosure's proved fields onto it stays open (MD-1).
/-- info: 'CSD.RecordLayer.recordLayerClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.recordLayerClosure

-- MomentMapRace (record layer / MD-1 step 2b′, 2026-07-25): grounds the fibre-partition rates in the
-- Kähler geometry (feature 2 of §3c). bornRate_eq_momentMap: for a unit ψ the rate ‖ψ i‖² IS the
-- i-th Fubini-Study torus moment-map coordinate at [ψ] (corpus LF4/MomentMap.momentMap) — forced by
-- the Kähler structure, not injected. bornRate_eq_inner_sq: hence = the corpus Born weight ‖⟨eᵢ,ψ⟩‖²
-- (FiniteQMClosure.born_frequency target). DeIsolationInteraction: the kinematic interface (pointer
-- with moment-map basins) ⟹ Born (.born). Open: realising the interface from a Hamiltonian H_int(M).
/-- info: 'CSD.RecordLayer.bornRate_eq_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornRate_eq_momentMap

/-- info: 'CSD.RecordLayer.bornRate_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornRate_eq_inner_sq

/-- info: 'CSD.RecordLayer.DeIsolationInteraction.born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.DeIsolationInteraction.born

-- Measurement (record layer / MD-1, 2026-07-25): the architecture in one object — context (measurement
-- type, fixes the basins/probabilities) + unknown microstate ξ → outcome (the basin it occupies) →
-- record. outcome_eq_some_iff (microstate selects its basin), record_of_mem_basin (combined result IS
-- the record ⟨context,outcome,time⟩), bornMeasurement_prob (basins set the probabilities = ‖ψ i‖²),
-- bornMeasurement_prob_momentMap (= the Kähler moment map, forced not injected), bornMeasurement_ae_total
-- (a.e. microstate yields a record). Assembles the proven pieces; the physical flow H_int(M) stays open.
/-- info: 'CSD.RecordLayer.Measurement.record_of_mem_basin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.Measurement.record_of_mem_basin

/-- info: 'CSD.RecordLayer.Measurement.bornMeasurement_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.Measurement.bornMeasurement_prob

/-- info: 'CSD.RecordLayer.Measurement.bornMeasurement_prob_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.Measurement.bornMeasurement_prob_momentMap

-- The Born rule as LLN over the unknown microstate (2026-07-25): the whole probabilistic content is
-- the strong law — i.i.d. typical microstates (law fibreTypicality) give outcome-i frequency → the
-- basin measure ‖ψ i‖² = the moment map. Randomness = ignorance of the initial condition; no extra
-- dynamical postulate (the "de-isolation flow" is just the deterministic microstate→basin map).
/-- info: 'CSD.RecordLayer.Measurement.bornMeasurement_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.Measurement.bornMeasurement_frequency

-- ProjectiveRecord (record layer migration onto the actual Σ, 2026-07-25): the record layer instantiated
-- on the corpus's REAL model — Σ = CPN(M+1), events = the corpus's own bornRegion, outcome map =
-- bornOutcome, measure = fubiniStudyMeasure. projRecordSemantics (P5 RecordSemantics on CPN, measurable
-- + exclusive from bornRegion_measurable_uncond/bornRegion_pairwiseDisjoint); bornOutcome_eq_record (the
-- corpus outcome map IS the record); fubiniStudy_projRecord (FS typicality of the record event = ‖⟨eᵢ,ψ⟩‖²);
-- projRecord_frequency (Born = LLN over the unknown microstate on the real Σ = FiniteQMClosure.born_frequency
-- conclusion, carried by the record-layer RecordSemantics). Not a parallel toy — the real Born machinery.
/-- info: 'CSD.RecordLayer.projRecordSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.projRecordSemantics

/-- info: 'CSD.RecordLayer.bornOutcome_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornOutcome_eq_record

/-- info: 'CSD.RecordLayer.fubiniStudy_projRecord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.fubiniStudy_projRecord

/-- info: 'CSD.RecordLayer.projRecord_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.projRecord_frequency

-- FibredSigma (record layer / MD-1, 2026-07-25): the ontic space assembled as Σ = base × fibre =
-- CPN n × ℝ — the base the EPISTEMIC projective point (pinned to [ψ] for a sharp prep,
-- baseProj_sharpTypicality), the fibre the ONTIC record coordinate (carves the Born partition). The
-- sharp typicality δ_[ψ] ⊗ fibreTypicality gives Born as the fibre event's typicality
-- (sharpTypicality_fibredEvent = ‖ψ i‖² = the moment map). The epistemic(base)/ontic(fibre) split of
-- Papers C/D made literal — ties FibreRecord to the projective base.
/-- info: 'CSD.RecordLayer.baseProj_sharpTypicality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.baseProj_sharpTypicality

/-- info: 'CSD.RecordLayer.sharpTypicality_fibredEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sharpTypicality_fibredEvent

/-- info: 'CSD.RecordLayer.sharpTypicality_fibredEvent_momentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sharpTypicality_fibredEvent_momentMap

-- BasisMeasurement (record layer, arbitrary observable, 2026-07-25): the record layer for a general
-- orthonormal basis b (any observable). bornRateBasis_eq_inner_sq (outcome prob = ‖⟨bᵢ,ψ⟩‖²),
-- sum_bornRateBasis_unit (probability vector), bornMeasurementBasis_prob (the general measurement's
-- outcome-i probability = ‖⟨bᵢ,ψ⟩‖²). Change of basis via the isometry b.repr.
/-- info: 'CSD.RecordLayer.bornMeasurementBasis_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornMeasurementBasis_prob

/-- info: 'CSD.RecordLayer.bornRateBasis_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.bornRateBasis_eq_inner_sq

-- KSigmaRecord (record layer on the closure's actual product Σ, 2026-07-25): the record layer on
-- Σ = KSigma(M+1) = CPN × T² (the FiniteQMClosure space). kSigmaRecordSemantics (P5 RecordSemantics,
-- events = bornRegion lifted through π = Prod.fst); born_frequency_region_eq_record (the region
-- FiniteQMClosure.born_frequency lands in, π⁻¹'bornRegion, is DEFINITIONALLY the record event — the
-- record layer is wired to the closure's actual field, field rewrite unnecessary); bornOutcome_base_eq_record.
/-- info: 'CSD.RecordLayer.kSigmaRecordSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.kSigmaRecordSemantics

/-- info: 'CSD.RecordLayer.born_frequency_region_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.born_frequency_region_eq_record

-- OscillatorBorn (EFT Stage 0: the truncated CV mode as a record-layer measurement, 2026-07-25). The
-- oscillator Hamiltonian is diagonal → number basis = standard basis → the mode's number/energy
-- measurement IS the record-layer measurement. numberMeasurement_prob (= ‖⟨n|ψ⟩‖²),
-- numberMeasurement_frequency (Born = LLN over the unknown microstate, inherited), numberBornProb_embed
-- (cutoff-independence: raising the truncation N→M≥N leaves each level's Born prob unchanged). The
-- gate step toward the EFT direction (QM→CV→EFT); single mode at finite cutoff, continuum not taken.
/-- info: 'CSD.CV.numberMeasurement_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.numberMeasurement_prob

/-- info: 'CSD.CV.numberMeasurement_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.numberMeasurement_frequency

/-- info: 'CSD.CV.numberBornProb_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.numberBornProb_embed

-- FieldModes (EFT Stage 1: a free scalar field at a cutoff as a product of modes, 2026-07-25). Field
-- Hilbert space = tensor product of K truncated modes, indexed by occupation configs Fin K → Fin N.
-- fieldHamiltonian_mulVec_single (free field = sum of oscillators, diagonal, eigenvalue ∑ oscEnergy),
-- fieldEnergy_cutoff_independent, sum_fieldBornProb_unit (config Born distribution), norm_sq_tprodState
-- (product state ‖⊗ψₖ‖²=∏‖ψₖ‖² — composite/tensor structure), and modeMarginal_tprod_unit (MODE-WISE
-- BORN: the marginal of a product state = the single-mode Born weight ‖ψ_{k₀} n‖²). Free field, cutoff.
/-- info: 'CSD.CV.fieldHamiltonian_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.fieldHamiltonian_mulVec_single

/-- info: 'CSD.CV.norm_sq_tprodState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.norm_sq_tprodState

/-- info: 'CSD.CV.modeMarginal_tprod_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.modeMarginal_tprod_unit

-- Dispersion (EFT Stage 2a: relativistic dispersion ω(m,p) = √(p²+m²), 2026-07-27). The mode
-- frequencies that make the mode sum a RELATIVISTIC field: omega_sq_sub_sq is the MASS SHELL
-- ω²−p²=m² (the Lorentz-invariant content, and why m is called the mass); abs_le_omega (|p| ≤ ω —
-- excitations do not outrun the light cone); abs_mass_le_omega + omega_zero (the MASS GAP |m| ≤ ω,
-- attained at rest); omega_massless (ω = |p| exactly, the light cone); omega_le_newtonian (ω ≤ m +
-- p²/2m, the non-relativistic limit as a clean INEQUALITY, no asymptotics); omega_mono. The field:
-- relFieldHamiltonian_mulVec_single + _isHermitian (still DIAGONAL in the configuration basis, so
-- the OscillatorBorn record-layer account carries over verbatim — only the eigenvalues change),
-- relFieldEnergy_quantum (THE HEADLINE: one quantum in mode k₀ costs exactly ω(m, p k₀), so the
-- excitations ARE relativistic particles of mass m — the dispersion is about the particle content,
-- not a parameter choice), relFieldEnergy_vacuum (zero-point ½∑ω), relFieldEnergy_cutoff_independent.
/-- info: 'CSD.CV.omega_sq_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_sq_sub_sq

/-- info: 'CSD.CV.abs_le_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.abs_le_omega

/-- info: 'CSD.CV.abs_mass_le_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.abs_mass_le_omega

/-- info: 'CSD.CV.omega_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_zero

/-- info: 'CSD.CV.omega_massless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_massless

/-- info: 'CSD.CV.omega_le_newtonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_le_newtonian

/-- info: 'CSD.CV.omega_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.omega_mono

/-- info: 'CSD.CV.relFieldHamiltonian_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldHamiltonian_mulVec_single

/-- info: 'CSD.CV.relFieldHamiltonian_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldHamiltonian_isHermitian

/-- info: 'CSD.CV.relFieldEnergy_quantum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldEnergy_quantum

/-- info: 'CSD.CV.relFieldEnergy_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldEnergy_vacuum

/-- info: 'CSD.CV.relFieldEnergy_cutoff_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.relFieldEnergy_cutoff_independent

-- ModeLocality (EFT Stage 2b: commuting algebras of disjoint mode sets, 2026-07-27). The HAAG-
-- KASTLER kinematic locality axiom at the finite cutoff: commute_of_disjointSupport -- operators
-- supported on DISJOINT mode sets commute (A*B = B*A), so observables of disjoint regions are
-- jointly measurable and the record layer can assign them outcomes simultaneously. Proof = the
-- uniqueness of the intermediate configuration (one surviving term per product, equal in pairs by
-- the support conditions). NOT VACUOUS: modeOp_supportedOn exhibits SupportedOn {k₀} for every
-- single-mode matrix, and commute_modeOp is the concrete instance at distinct modes.
-- HONEST SCOPE (see the file's "does NOT claim" section): this is SUBSYSTEM locality, spatial only
-- under the position-space reading of the modes (CV/Position.lean). Continuum microcausality
-- [φ(x),φ(y)]=0 at spacelike separation is NOT proved and does NOT hold exactly at a finite cutoff;
-- it needs the continuum limit, deliberately deferred (CV/ApproxCCR.no_exact_finite_ccr).
/-- info: 'CSD.CV.commute_of_disjointSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commute_of_disjointSupport

/-- info: 'CSD.CV.modeOp_supportedOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.modeOp_supportedOn

/-- info: 'CSD.CV.commute_modeOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.CV.commute_modeOp

-- HatBox (context-fixed qubit measurement infra / A7, 2026-07-26): the Archimedes hat-box, the
-- single-axis crux integral. hatBox_moment: the Fubini-Study average over ℂℙ¹ of the Bloch height
-- |λ·n| = |2·momentMap - 1| is 1/2. NOT raw S² integration — reduces to the proved moment coordinate
-- being Uniform[0,1] (fs_moment_pushforward_uniform) + the 1D integral ∫_{[0,1]}|2t-1|=1/2
-- (integral_abs_two_mul_sub_one). The foundation for the qubit context-fixed hemisphere+spread proof.
/-- info: 'CSD.LF4.hatBox_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.hatBox_moment

/-- info: 'CSD.LF4.integral_abs_two_mul_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.integral_abs_two_mul_sub_one

-- spread-density normalisation (context-fixed qubit, 2026-07-26): ρ = 4·max(2·momentMap−1,0) (Bloch
-- 4(m·λ)₊) integrates to 1 against μ_FS (spreadDensity_normalized) via the moment coordinate Uniform[0,1]
-- + integral_max_two_mul_sub_one_zero (∫_{[0,1]}max(2t−1,0)=1/4). The "½"-term ingredient of §2.
/-- info: 'CSD.LF4.spreadDensity_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.spreadDensity_normalized

-- QubitReflection (context-fixed qubit, brick 1, 2026-07-26): the reflection identity — the C-term crux
-- of §2. reflect_sq_add: ‖⟨ψ,φ⟩‖² + ‖⟨ψ,R_nφ⟩‖² = 2cu + 2(1−c)(1−u), R_n φ = 2⟨n,φ⟩·n − φ. Pure ℂ²
-- linear algebra: completeness of {n,n^⊥} (`completeness`), Parseval (`parseval_vec`), parallelogram.
/-- info: 'CSD.LF4.reflect_sq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.reflect_sq_add

/-- info: 'CSD.LF4.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.completeness

/-- info: 'CSD.LF4.parseval_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.parseval_vec

-- BlochProjection (context-fixed qubit foundation, 2026-07-26): general-axis Born weight
-- blochProj a p = |⟨a,rep p⟩|²/‖rep p‖² — shared foundation for the hemisphere cut (blochProj n) and
-- the spread density (blochProj ψ). blochProj_smul: U(N)-equivariance; blochProj_measurable: Borel.
/-- info: 'CSD.LF4.blochProj_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_smul

/-- info: 'CSD.LF4.blochProj_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_measurable

/-- info: 'CSD.LF4.blochProj_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_mk

-- AxisBridge (context-fixed qubit, 2026-07-26): general axis ↦ reference axis for μ_FS integrals.
-- blochProj_integral_bridge: ∫ f(blochProj n p) dμ_FS = ∫ f(momentMap p 0) dμ_FS (unit n), via
-- fubiniStudyMeasure_smul_invariant. Lifts hatBox_moment/spreadDensity_normalized to any axis:
-- hatBox_axis (∫|2·blochProj n−1|=½), spreadDensity_normalized_axis (∫4(2·blochProj n−1)₊=1).
/-- info: 'CSD.LF4.blochProj_integral_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_integral_bridge

/-- info: 'CSD.LF4.hatBox_axis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.hatBox_axis

/-- info: 'CSD.LF4.spreadDensity_normalized_axis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.spreadDensity_normalized_axis

-- QubitDipole (context-fixed qubit, brick 3 infra, 2026-07-26): R_n = 2|n⟩⟨n|−I as a Hermitian
-- unitary (reflMat_mem_unitaryGroup, reflU), its action reflMat_toEuclideanLin (R_n w = 2⟨n,w⟩•n−w),
-- and blochProj_refl_fixes (R_n fixes the n-coordinate). The dipole change-of-variables engine.
/-- info: 'CSD.LF4.reflMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.reflMat_mem_unitaryGroup

/-- info: 'CSD.LF4.reflMat_toEuclideanLin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.reflMat_toEuclideanLin

/-- info: 'CSD.LF4.blochProj_refl_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_refl_fixes

-- Dipole (context-fixed qubit, brick 3, 2026-07-26): D = ∫ rsign(2·blochProj n−1)(2·blochProj ψ−1)
-- dμ_FS = (2c−1)/2, c=|⟨n,ψ⟩|². Via R_n reflection (μ_FS-preserving, fixes n) + reflect_sq_add
-- (reflSum) linearising the paired density + hatBox_axis. The dipole term of the qubit Born rule.
/-- info: 'CSD.LF4.dipole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.dipole

/-- info: 'CSD.LF4.reflSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.reflSum

-- CrossTerm (context-fixed qubit, brick 2, 2026-07-26): T = ∫ rsign(2·blochProj n−1)|2·blochProj ψ−1|
-- dμ_FS = 0 — the antipode symmetry (Haar right-mult by the e₀↔e₁ swap flips both Born coords via the
-- ONB-complement Parseval flip inner_unitary_flip), so T = −T. The monopole cross-term vanishing.
/-- info: 'CSD.LF4.crossTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.crossTerm

/-- info: 'CSD.LF4.inner_unitary_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.inner_unitary_flip

-- ★ QubitBorn (context-fixed qubit, brick 5 = THE PAYOFF, 2026-07-26): the qubit Born rule derived
-- from the CSD spread density + context-fixed hemisphere against the Fubini–Study typicality measure:
-- ∫ ½(1+rsign(2·blochProj n−1))·4(2·blochProj ψ−1)₊ dμ_FS = |⟨n,ψ⟩|². Assembles the four component
-- integrals (∫(2s−1)=0, ∫|2s−1|=½ hat-box, dipole=(2c−1)/2, crossTerm=0) = c. Foundational-triple.
/-- info: 'CSD.LF4.qubitBorn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.qubitBorn

/-- info: 'CSD.LF4.blochProj_integral_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.blochProj_integral_half

-- PointerArena (2026-08-03, SigmaLayer/PointerArena.lean; pointer-witness-plan.md brick 0 — the
-- smooth-Hamiltonian route's kinematic floor, architecture confirmed 2026-08-03). The compact
-- Kähler pointer ℂℙ^K replacing the torus register (the flux correction's repair): open,
-- disjoint, positive-FS-measure ready/record regions via the pointer moment map, and the arena
-- KSigma N × ℂℙ^K with pointerLiouville = kMuL ⊗ μ_FS^ptr. Key structural fact: arenaReady_pos —
-- a positive-measure apparatus-ready state EXISTS on this arena (contrast globalBasin_ae_total,
-- where a.e. every point already carries a record). Kinematics only; the propagator is bricks 1–4.
/-- info: 'CSD.RecordLayer.recordRegion_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.recordRegion_pairwiseDisjoint

/-- info: 'CSD.RecordLayer.readyRegion_disjoint_recordRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.readyRegion_disjoint_recordRegion

/-- info: 'CSD.RecordLayer.recordRegion_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.recordRegion_pos

/-- info: 'CSD.RecordLayer.readyRegion_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.readyRegion_pos

/-- info: 'CSD.RecordLayer.arenaReady_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.arenaReady_pos

-- PointerRotation (2026-08-03, SigmaLayer/PointerRotation.lean; pointer-witness-plan.md brick 1).
-- The fixed-outcome pointer rotation: Hermitian generator h_j = |f0><f_{j+1}| + |f_{j+1}><f0|
-- (pointerH_isHermitian), whose rotation family pointerRot θ j = 1 + (cosθ−1)•P_j − (i sinθ)•h_j
-- is a CONTINUOUS ONE-PARAMETER UNITARY GROUP: group law (pointerRotU_add), unitarity via
-- rotᴴ = rot(−θ), continuity (continuous_pointerRotU) — the properties shearEvolve provably
-- lacks (shearEvolve_not_continuous). Quarter turn transports ready → record projectively
-- (pointerRotU_pi_div_two_ready); FS measure preservation is unitary invariance
-- (pointerRotU_measurePreserving). Honest scope: the exp(−iθh_j) identification is brick 5.
/-- info: 'CSD.RecordLayer.pointerH_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerH_isHermitian

/-- info: 'CSD.RecordLayer.pointerRot_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRot_mem_unitaryGroup

/-- info: 'CSD.RecordLayer.pointerRotU_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRotU_add

/-- info: 'CSD.RecordLayer.continuous_pointerRotU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_pointerRotU

/-- info: 'CSD.RecordLayer.pointerRotU_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRotU_measurePreserving

/-- info: 'CSD.RecordLayer.pointerRotU_pi_div_two_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRotU_pi_div_two_ready

-- PointerCoupling (2026-08-03, SigmaLayer/PointerCoupling.lean; pointer-witness-plan.md brick 2a,
-- generator half). The selector-modulated coupling: couplingH w = Σⱼ wⱼ•hⱼ Hermitian for every
-- real weight vector; couplingU w = exp((π/2)•(−i•couplingH w)) UNITARY (skew-Hermitian
-- exponential; the hⱼ do NOT commute — genuine exp, no closed form). ★ pointerRot_eq_exp: the
-- HAMILTONIAN-GENERATION IDENTIFICATION — brick 1's closed form IS exp(θ•(−i•hⱼ)), by ODE
-- uniqueness (eq_exp_of_hasDeriv); brick 5's single-plane half, pulled forward because the
-- landing theorem reads pure cells through couplingU_single = pointerRot (π/2) j. Entrywise
-- Lipschitz continuity in the weights (continuous_couplingU_entry) via the Duhamel bound + the
-- NEW staged entry bound Matrix.norm_entry_le_l2_opNorm (L2OpNormEntry.lean) — stated in the
-- plain Pi topology, no scoped norm instances in the statement.
/-- info: 'CSD.RecordLayer.couplingH_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.couplingH_isHermitian

/-- info: 'CSD.RecordLayer.couplingU_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.couplingU_mem_unitaryGroup

/-- info: 'CSD.RecordLayer.pointerRot_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRot_eq_exp

/-- info: 'CSD.RecordLayer.couplingU_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.couplingU_single

/-- info: 'CSD.RecordLayer.continuous_couplingU_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_couplingU_entry

/-- info: 'Matrix.norm_entry_le_l2_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Matrix.norm_entry_le_l2_opNorm

-- PointerWeights (2026-08-03, SigmaLayer/PointerWeights.lean; pointer-witness-plan.md brick 2b).
-- The selector-modulated weight field and the arena propagator. Weights are CIRCLE-INTRINSIC
-- trapezoids clamp((r_j/2 − dist(θ₁, cellMid_j))/ε) with rates read at the base point
-- (ContextField, no preparation) — so joint continuity is a composition, no lift, no seam.
-- ★ continuous_pointerEvolve: THE FULL ARENA PROPAGATOR IS CONTINUOUS — the theorem
-- shearEvolve_not_continuous proves no torus-register witness can have; proof descends through
-- the open quotient id × mk' (IsOpenQuotientMap.prodMap) to entrywise-continuous matrix data.
-- pointerEvolve_measurePreserving: Liouville preservation as a skew product (sector conserved,
-- FS-preserving unitary on each pointer slice). pointerEvolve_pure: on shrunk cells the
-- propagator IS the brick-1 quarter rotation (weights collapse to Pi.single) — the landing seed;
-- the cell-geometry distance facts are brick 3's obligation.
/-- info: 'CSD.RecordLayer.continuous_pointerWeights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_pointerWeights

/-- info: 'CSD.RecordLayer.pointerWeights_eq_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerWeights_eq_single

/-- info: 'CSD.RecordLayer.continuous_pointerEvolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_pointerEvolve

/-- info: 'CSD.RecordLayer.pointerEvolve_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerEvolve_measurePreserving

/-- info: 'CSD.RecordLayer.pointerEvolve_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerEvolve_pure

-- PointerLanding (2026-08-03, SigmaLayer/PointerLanding.lean; pointer-witness-plan.md brick 3).
-- The landing geometry. cellMid_dist_ge: distinct CDF-cell midpoints are ≥ (r_j+r_k)/2 apart on
-- the circle (UnitAddCircle.norm_eq + round case analysis + the loSum interval ordering);
-- shrunk_dist_other: triangle inequality discharges pointerEvolve_pure's second hypothesis — no
-- per-cell inclusion geometry needed. momentMap_pointerRot_smul: m_{j+1}(U_j(π/2)•q) = m_0(q)
-- EXACTLY, so the open ready region maps into the open record region with margin (δ ≤ 1/2).
-- ★ pointer_landing: sector in the shrunk cell of j + pointer ready ⇒ the CONTINUOUS
-- Liouville-preserving propagator lands in arenaRecord j — record creation with the ontic sector
-- selecting the outcome. volume_shrunkCell_slice: the shrunk slice carries selector volume
-- exactly r_j − 2ε (AddCircle.volume_closedBall) — the ε-Born seed; the 2ε deficit is the
-- no_everywhere_correlation corridor, priced, never hidden.
/-- info: 'CSD.RecordLayer.cellMid_dist_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.cellMid_dist_ge

/-- info: 'CSD.RecordLayer.shrunk_dist_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.shrunk_dist_other

/-- info: 'CSD.RecordLayer.momentMap_pointerRot_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.momentMap_pointerRot_smul

/-- info: 'CSD.RecordLayer.pointer_landing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_landing

/-- info: 'CSD.RecordLayer.measurableSet_shrunkCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.measurableSet_shrunkCell

/-- info: 'CSD.RecordLayer.volume_shrunkCell_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.volume_shrunkCell_slice

-- PointerProtocol (2026-08-03, SigmaLayer/PointerProtocol.lean; pointer-witness-plan.md brick 4a).
-- The smooth witness in the standard record architecture: MeasurementProtocol on the pointer
-- arena with evolve = ramped exponential of the selector-modulated coupling. The two-time law is
-- THE GROUP PROPERTY of the exponential (couplingUAt_mul, exp_add_of_commute) — vs the swap's
-- eight-case crossing proof; persistence is FREEZING (ramp constant after readout ⇒ identity ⇒
-- PointerInvariantOn discharged outright); the correlation obligation is the landing theorem
-- (pointerProtocol_correlatesOn, sectors = shrunk cell × ready). ★ Joint time–state continuity
-- (continuous_pointerRampedEvolve, definitionally the protocol propagator): the two-sided
-- Duhamel estimates (weights + angle: norm_couplingUAt_sub_time swaps the roles of time and
-- generator) squeeze each entry (continuous_couplingUAt_entry_joint); the projective action by
-- the generic open-quotient descent continuous_unitaryFamily_smul.
/-- info: 'CSD.RecordLayer.couplingUAt_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.couplingUAt_mul

/-- info: 'CSD.RecordLayer.norm_couplingUAt_sub_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.norm_couplingUAt_sub_time

/-- info: 'CSD.RecordLayer.continuous_couplingUAt_entry_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_couplingUAt_entry_joint

/-- info: 'CSD.RecordLayer.continuous_unitaryFamily_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_unitaryFamily_smul

/-- info: 'CSD.RecordLayer.continuous_pointerRampedEvolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_pointerRampedEvolve

/-- info: 'CSD.RecordLayer.pointerProtocol_correlatesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerProtocol_correlatesOn

/-- info: 'CSD.RecordLayer.pointerProtocol_pointerInvariantOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerProtocol_pointerInvariantOn

-- PointerBorn (2026-08-03, SigmaLayer/PointerBorn.lean; pointer-witness-plan.md brick 4b —
-- closes brick 4). The ε-Born sandwich for the ready-CONDITIONED preparation
-- pointerPrep = epistemicMeasure ⊗ FS[|ready] (legitimate: readyRegion_pos — NO Dirac
-- calibration posit, unlike the swap): pointerPrep_sector_measure = r_j − 2ε EXACTLY (the
-- brick-3 slice volume through the globalBasin_prob dirac-slice pattern);
-- ★ pointer_born_lower (containment) and ★ pointer_born_upper — the upper bound needs NO cell
-- geometry: disjoint sectors + the other N−1 lower bounds crowd out everything above
-- r_j + 2(N−1)ε in a probability space. ★★ smoothWitnessClosure: ONE witness carrying protocol
-- + joint time–state continuity + Liouville preservation + positive-measure ready state +
-- record creation (sector-selected) + structural persistence + ε-Born; instantiated on the
-- canonical moment-map context (smoothWitnessClosureCanonical). The smooth horn of the
-- no_everywhere_correlation trade-off — complementing, never displacing, the exact-record
-- piecewise closures.
/-- info: 'CSD.RecordLayer.pointerPrep_sector_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerPrep_sector_measure

/-- info: 'CSD.RecordLayer.pointer_born_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_born_lower

/-- info: 'CSD.RecordLayer.pointer_born_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_born_upper

/-- info: 'CSD.RecordLayer.smoothWitnessClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.smoothWitnessClosure

/-- info: 'CSD.RecordLayer.smoothWitnessClosureCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.smoothWitnessClosureCanonical

-- PointerGeneration (2026-08-03, SigmaLayer/PointerGeneration.lean; pointer-witness-plan.md
-- brick 5 -- COMPLETES THE LADDER). * rampedU_schrodinger: on the interaction window the ramped
-- propagator satisfies the SCHRODINGER EQUATION U' = U*(-i*H_eff) with the explicit HERMITIAN
-- generator H_eff = (pi/2) * couplingH w (pointerHeff_isHermitian) -- the Hamiltonian-generation
-- statement at the formalisable level, with no flux obstruction (projective pointer, H^1 = 0);
-- the symplectic/moment-map reading stays the A1/A3-scoped prose boundary (MATHLIB-GAPS).
-- pointerEvolve_base_marginal_unchanged: the stroke leaves every sector marginal untouched --
-- records WITHOUT back-reaction, the smooth counterpart of shear_base_marginal_unchanged;
-- collapse stays on the swap/join witnesses, composition = the recorded M-L extension.
/-- info: 'CSD.RecordLayer.pointerHeff_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerHeff_isHermitian

/-- info: 'CSD.RecordLayer.rampedU_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.rampedU_schrodinger

/-- info: 'CSD.RecordLayer.pointerEvolve_base_marginal_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerEvolve_base_marginal_unchanged

-- LocalLuders (2026-08-03, SigmaLayer/LocalLuders.lean; dynamical no-signalling brick 1).
-- A local B-measurement on the composite acts by the coordinate-form local projectors
-- P_j = 1_A (x) |f_j><f_j| (localProjB): idempotent, identity-resolving (sum_localProjB),
-- norm-resolving Born weights (sum_normSq_localProjB). ★★ reduceA_localLuders_mixture — THE
-- STATICS CORE OF DYNAMICAL NO-SIGNALLING: the Born-weighted mixture of post-measurement
-- A-marginals equals the pre-measurement A-marginal (zero-weight branches carry weight 0, no
-- positivity smuggled). Unnormalised core traceRight_sum_vecOuter_localProjB: tracing out B
-- collapses the Lüders sum entrywise. Brick 2 = wire to BlockLudersObligation through the
-- Fin (nA·nB) index bridge; brick 3 = the eraser process (mark then erase, sequential).
/-- info: 'CSD.RecordLayer.sum_localProjB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sum_localProjB

/-- info: 'CSD.RecordLayer.sum_normSq_localProjB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sum_normSq_localProjB

/-- info: 'CSD.RecordLayer.traceRight_sum_vecOuter_localProjB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.traceRight_sum_vecOuter_localProjB

/-- info: 'CSD.RecordLayer.reduceA_localLuders_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.reduceA_localLuders_mixture

-- LocalBlockBridge (2026-08-03, SigmaLayer/LocalBlockBridge.lean; dynamical no-signalling
-- brick 2). Under finProdFinEquiv, the block structure of a local B-measurement is the second
-- projection (localBlock) and ★ the degenerate-Lüders block projector IS the local projector
-- (toComposite_blockProj — a definitional identity, not an analogy), with isometric transport
-- so block Born weights = local Born weights. ★★ reduceA_blockLuders_mixture — DYNAMICAL
-- NO-SIGNALLING in the dynamics' own vocabulary: the Born-weighted mixture of A-marginals of
-- the post-states the JOIN WITNESS delivers (BlockLudersObligation localBlock, inhabited by
-- joinWitness_blockLuders; weights per degenerate_selector_born) equals the A-marginal of the
-- preparation. Brick 3 (remaining): the measure-level ensemble integral + the eraser process.
/-- info: 'CSD.RecordLayer.toComposite_blockProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.toComposite_blockProj

/-- info: 'CSD.RecordLayer.norm_blockProj_localBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.norm_blockProj_localBlock

/-- info: 'CSD.RecordLayer.reduceA_blockLuders_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.reduceA_blockLuders_mixture

-- LocalLudersBasis (2026-08-03, SigmaLayer/LocalLudersBasis.lean; dynamical no-signalling
-- brick 3a). The local Lüders map for an ARBITRARY orthonormal basis on the measured factor:
-- localProjOn g j = 1_A (x) |g_j><g_j| in coordinate form; the computational case recovers
-- localProjB exactly (localProjOn_basisFun). Identity resolution by basis expansion
-- (sum_localProjOn), Born weights resolve the norm by Parseval per slice
-- (sum_normSq_localProjOn), and ★★ reduceA_localLudersOn_mixture — MARGINAL INVARIANCE IN
-- EVERY BASIS: Alice cannot detect Bob's outcome OR his basis choice; Parseval
-- (sum_inner_mul_inner) does the work the ite-collapse did in brick 1. Brick 3b: the 2⊗2
-- eraser instantiation (computational mark = which-path/no fringe; ± erase = eraserOut
-- fringes + the exact dark zero).
/-- info: 'CSD.RecordLayer.localProjOn_basisFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.localProjOn_basisFun

/-- info: 'CSD.RecordLayer.sum_localProjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sum_localProjOn

/-- info: 'CSD.RecordLayer.sum_normSq_localProjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.sum_normSq_localProjOn

/-- info: 'CSD.RecordLayer.traceRight_sum_vecOuter_localProjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.traceRight_sum_vecOuter_localProjOn

/-- info: 'CSD.RecordLayer.reduceA_localLudersOn_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.reduceA_localLudersOn_mixture

-- EraserDynamics (2026-08-03, Empirical/CSD/EraserDynamics.lean; dynamical no-signalling
-- brick 3b — the eraser PROCESS). The two eraser arms are the corpus's local Lüders maps on
-- the Bell path–marker state. MARK (computational marker): localProjB_bellE — the post-state
-- IS the which-path product |j⟩⊗|j⟩; marked_no_fringe — screen rate 1/2 at EVERY phase (the
-- fringe dies dynamically). ERASE (± marker, an instance of localProjOn at the genuine
-- OrthonormalBasis pmBasis): ★ erased_amp — the dynamical post-state's screen amplitudes are
-- EXACTLY √2·eraserOut, so every QuantumEraserVolume statistic is a statement about the state
-- the measurement dynamics produces: erased_rate (conditional fringes), erased_dark (the
-- exact dark-fringe zero, from the dynamics), erased_weight (marker weights 1/2 — the
-- dynamical eraser_marker_marginal). With reduceA_localLudersOn_mixture: mark kills the
-- fringe, erase restores it in the conditioned records, nothing reaches Alice's marginal.
/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.localProjB_bellE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.localProjB_bellE

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.marked_no_fringe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.marked_no_fringe

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.erased_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.erased_amp

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.erased_dark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.erased_dark

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.erased_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.erased_rate

/-- info: 'CSD.Empirical.CSDBridge.EraserDynamics.erased_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserDynamics.erased_weight

-- EraserSequential (2026-08-03, Empirical/CSD/EraserSequential.lean; the row's residue). The
-- two-stroke composition, in the decisive order: MARK FIRST (record exists), THEN ERASE.
-- seqProfile_eq: the erase stroke only RESCALES the recorded ray |j⟩; weights stay 1/2
-- (sequential_erase_weight); ★ sequential_no_revival — the screen rate stays 1/2 at every
-- phase, port, and marker outcome: once a record exists, no later marker measurement revives
-- the fringe. Records are statistically irreversible — the statistical face of
-- relocation-with-storage. (The other residue, the measure-level ensemble integral, is closed
-- as definitional: for finite outcomes the post ray-ensemble IS the discrete mixture and its
-- barycenter statement IS reduceA_localLudersOn_mixture.)
/-- info: 'CSD.Empirical.CSDBridge.EraserSequential.seqProfile_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserSequential.seqProfile_eq

/-- info: 'CSD.Empirical.CSDBridge.EraserSequential.sequential_erase_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserSequential.sequential_erase_weight

/-- info: 'CSD.Empirical.CSDBridge.EraserSequential.sequential_no_revival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.EraserSequential.sequential_no_revival

-- MeasurementCapstone (2026-08-03, SigmaLayer/MeasurementCapstone.lean; the second review's
-- step 4). ★★★ projectiveMeasurementCapstone — the corpus's four measurement closures as ONE
-- Prop, for every Hermitian generator, base point, and unit preparation: rank_one
-- (unifiedArenaClosure — one arena, one Liouville family), every_basis
-- (measurement_covariance — the apparatus basis is a parameter, not preferred structure),
-- degenerate (joinWitness_blockLuders — every block structure, ψ-dependent Lüders through
-- Liouville-preserving dynamics), smooth (smoothWitnessClosureCanonical — the ε-horn at every
-- ε, as Nonempty since the closure carries its protocol), generation (rampedU_schrodinger as
-- a field — added 2026-08-03, fourth review). The fields quantify over different witnesses BY
-- DESIGN: the two-horn framing (author decision 2026-08-03). New prose cites this one
-- theorem; the constituent closures remain as the construction record.
/-- info: 'CSD.RecordLayer.projectiveMeasurementCapstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.projectiveMeasurementCapstone

-- MixedSwap (2026-08-03, SigmaLayer/MixedSwap.lean; the mixed-preparations row). A mixed
-- preparation is two-stage sampling made a measure: mixedSwapPrep ρ = Σ_j λ_j • swapPrep [ψ_j]
-- over the spectral ensemble (a probability measure by eigenvalues_isProbability).
-- ★ mixed_swap_sector_born — THE MIXED DYNAMICAL BORN RULE: the mixture's mass on the
-- measurement protocol's outcome sector is exactly Tr(ρ|e_i⟩⟨e_i|); same propagator, same
-- sectors, classical ignorance responding as traceForm demands (spectral bridge
-- spectral_born_eq_traceForm via swap_sector_born per eigenray + traceForm_eq_pureEnsemble +
-- born_quadratic). Record creation/exclusivity/persistence are per-protocol facts, inherited
-- verbatim; the Bayes-conditioned mixture posts WERE a recorded extension and are now
-- delivered (MixedLuders, pinned below: mixed_post_bayes, mixed_luders_followup).
/-- info: 'CSD.RecordLayer.spectral_born_eq_traceForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.spectral_born_eq_traceForm

/-- info: 'CSD.RecordLayer.mixed_swap_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_swap_sector_born

-- PovmDynamics (2026-08-03, SigmaLayer/PovmDynamics.lean; the POVM/instrument-dynamics row).
-- A POVM is a projective measurement on a dilated space watched through an isometry — made
-- DYNAMICAL: prepare the dilated ray [Vψ] on the flat index and run the EXISTING degenerate
-- record protocol with the ancilla block structure localBlock N K (no new dynamics/sectors).
-- ★ povm_selector_born — THE DYNAMICAL POVM BORN RULE: the block selector's outcome-i sector
-- at [Vψ] carries exactly ⟨ψ, E_i ψ⟩ (degenerate_selector_born + born_transfer through the
-- spectral bridge sum_block_normSq_dilate).
-- ★ toComposite_blockProj_dilate — the record-layer block posts ARE the Naimark–Lüders posts
-- Π_i(Vψ) under the index transport.
-- ★★ povm_instrument — the join witness's post-marginals satisfy degenerate Lüders at the
-- dilated preparation: outcome i relocates the dilated system to [Π_i(Vψ)], the instrument of
-- the dilation (Liouville-preserving dynamics, not fiat).
-- ★★ naimarkInstrumentClosure / …Canonical — the bundle for every dilation, and via
-- canonicalNaimark for EVERY POVM. Honest scope: the instrument is dilation-relative (a POVM
-- does not determine its instrument); realising V as a unitary-plus-ancilla stroke = recorded
-- extension.
/-- info: 'CSD.RecordLayer.povm_selector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.povm_selector_born

/-- info: 'CSD.RecordLayer.toComposite_blockProj_dilate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.toComposite_blockProj_dilate

/-- info: 'CSD.RecordLayer.povm_instrument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.povm_instrument

/-- info: 'CSD.RecordLayer.naimarkInstrumentClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.naimarkInstrumentClosure

/-- info: 'CSD.RecordLayer.naimarkInstrumentClosureCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.naimarkInstrumentClosureCanonical

-- JoinClosure (2026-08-03, SigmaLayer/JoinClosure.lean; the degenerate one-protocol package,
-- fourth external review). The degenerate pieces existed as theorems on the join protocol but
-- were never packaged as ONE closure on ONE protocol.
-- ★ join_sector_born — the coarse dynamical Born mass: the canonical join preparation gives
-- the outcome-i sector exactly the block Born weight Σ_{j: b j = i}‖⟨e_j,ψ⟩‖², independently
-- of the ancilla calibration (quantified). Spine: preimage_sector_ae (sector = good-fibre
-- cylinder a.e.) + volume_goodTheta (the Dirac slice of degenerate_selector_born).
-- ★★ degenerateMeasurementClosure — ready/record/exclusivity/persistence + Liouville + the
-- Born mass + ψ-dependent degenerate Lüders (joinWitness_blockLuders), one structure, one
-- protocol, for every block structure and preparation. The capstone's degenerate field is
-- upgraded to this closure (was bare BlockLudersObligation).
/-- info: 'CSD.RecordLayer.join_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.join_sector_born

/-- info: 'CSD.RecordLayer.degenerateMeasurementClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.degenerateMeasurementClosure

-- MixedLuders (2026-08-03, SigmaLayer/MixedLuders.lean; the outcome-conditioned mixed update,
-- MixedSwap's recorded extension + the fourth review's row). Spine: mixedSwapPrep FACTORS
-- (mixedSwapPrep_eq_prod — the mixture lives on system-and-register, bank common), so the pure
-- swap_luders_born (stated for arbitrary probability μ12) applies verbatim; positivity is a
-- theorem (mixed_outcome_pos, from Tr(ρ|e_i⟩⟨e_i|) ≠ 0 through the spectral bridge).
-- ★ mixed_post_bayes — the conditioned post-ensemble IS the Bayes-posterior mixture: component
-- j carries λ_j·p_i|j / Tr(ρ|e_i⟩⟨e_i|) (prior × likelihood / evidence); engine = the newly
-- staged ProbabilityTheory.cond_finsetSum (Bayes for finite mixtures, hypothesis-free by
-- ℝ≥0∞ conventions).
-- ★★ mixed_luders_followup — THE RECORD, NOT THE PEDIGREE, FIXES THE POST-STATE: follow-up
-- statistics after outcome i on the mixture are c'.rate [e_i] — the pure rank-one Lüders
-- update; at rank one the record erases the classical ignorance. ρ ↦ Π_iρΠ_i/Tr(ρΠ_i)
-- dynamically. Degenerate-on-mixed = recorded extension (rides JoinClosure; posteriors do NOT
-- coincide at rank ≥ 2 and no claim is made that they do).
/-- info: 'ProbabilityTheory.cond_finsetSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProbabilityTheory.cond_finsetSum

/-- info: 'CSD.RecordLayer.mixed_post_bayes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_post_bayes

/-- info: 'CSD.RecordLayer.mixed_luders_followup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.mixed_luders_followup

-- PointerSmoothProfile (2026-08-03, SigmaLayer/PointerSmoothProfile.lean; the C^∞-ingredients
-- row, fourth external review's "continuous, not smooth"). Real.smoothTransition profiles with
-- the plateau interface VERBATIM IDENTICAL to the trapezoids' (same statements, same
-- hypotheses: =1 on the shrunk arc, =0 off the open arc, 0/π-halves around the stroke) — only
-- the corridor's shape changed.
-- contDiff_smoothClampDiv — the smooth clamp is C^∞ (what clampDiv could not be at its joins).
-- ★ contDiff_smoothArcWeight_lift — the arc weight's 1-periodic lift is C^∞ on the universal
-- cover: both circle-distance kinks fall inside plateaus (centre: 2ε < r; cut locus: r < 1),
-- and the transition zone sees a locally affine distance (round locally constant strictly
-- inside the half-integer window). The strongest formulation without a manifold structure on
-- the arena (that stays §2a-scoped with A1/A3).
-- SUBSTITUTED 2026-08-04 (BACKLOG B1): the profile primitives moved DOWN the import graph to
-- SigmaLayer/SmoothProfile.lean and pointerWeights is now built on smoothArcWeight, so the
-- witness USES the C^infinity profile rather than citing it. The plateau interface is
-- identical by construction, so every downstream landing/Born/protocol proof transferred with
-- no change. contDiff_pointerWeights_lift is the new smoothness statement, and it is what
-- makes {w_i, w_j} well-formed -- the prerequisite the joint-arena Poisson route turns on.
-- The TIME RAMP is deliberately still the trapezoid (not a phase-space function; swapping it
-- would put a rate factor in the capstone's generation field -- BACKLOG B1b).
/-- info: 'CSD.RecordLayer.contDiff_pointerWeights_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.contDiff_pointerWeights_lift

-- ★ smoothRampedU_schrodinger — SCHRÖDINGER AT EVERY TIME: the smooth ramp removes the open-
-- window restriction of rampedU_schrodinger (the corners are gone, as PointerGeneration's
-- honest scope predicted); outside [0,1] the ODE reads U̇ = 0 — persistence as an ODE.
-- Protocol re-instantiation = mechanical (identical interface), recorded.
/-- info: 'CSD.RecordLayer.contDiff_smoothClampDiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.contDiff_smoothClampDiv

/-- info: 'CSD.RecordLayer.contDiff_smoothArcWeight_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.contDiff_smoothArcWeight_lift

/-- info: 'CSD.RecordLayer.smoothRampedU_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.smoothRampedU_schrodinger

-- NullSeamWitness (2026-08-03, SigmaLayer/NullSeamWitness.lean; the "Cantor-horn" row, fourth
-- external review — delivered, and SIMPLER than the devil's-staircase sketch: the transition
-- between record regions dodges the record gap by crossing WHERE THE RECORD REGIONS KISS
-- (m₁ = m₂ = ½), touching the complement at one projective point; the crossing angle sweeps
-- continuously in the register, hitting π/4 exactly at the two cell boundaries.
-- ★ nullSeam_seam_null — the seam is TWO POINTS (nullSeamSign = infDist-to-arc difference:
-- negative exactly on the open first cell, positive exactly on the second, zero exactly at
-- the boundaries). ★ nullSeam_born_left/right — EXACT Born (r and 1−r, no ε; closedBall
-- sandwich + the two-point seam). ★★ continuous_nullSeamEvolve + Liouville preservation
-- (skew product, FS unitary invariance; the measure is NOT called Liouville — S¹ × ℂℙ² is
-- odd-dimensional hence not symplectic, naming corrected 2026-08-03 by the fifth review).
-- ★★ nullSeamClosure — THE THIRD HORN EXISTS.
-- THE TRILEMMA: each horn pays exactly one of — seams (piecewise), ε-Born (smooth witness),
-- Dirac calibration (this witness: exactness is at the calibrated ready point [f₀]; with a
-- positive-width ready region the seam fattens to O(δ) — the price collapse_accuracy_bound
-- already prices). Whether a fourth combination is impossible = recorded candidate no-go.
/-- info: 'CSD.RecordLayer.nullSeam_seam_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeam_seam_null

/-- info: 'CSD.RecordLayer.nullSeam_born_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeam_born_left

/-- info: 'CSD.RecordLayer.continuous_nullSeamEvolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.continuous_nullSeamEvolve

/-- info: 'CSD.RecordLayer.nullSeamClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeamClosure

-- JointFlowTransfer (2026-08-04, SigmaLayer/JointFlowTransfer.lean; BACKLOG A1 -- the
-- formalisable half of the joint-arena Hamiltonian route). Paper C A2 / TN6 want measurement
-- generated by a scalar on the WHOLE arena; the corpus's witness is fibrewise
-- (pointerEvolve_fst freezes the base by rfl). A genuine joint flow BACK-REACTS, and the
-- worry was that this destroys the landing/Born analysis. It does not:
-- ★★ IsJointLift.outcomeSector_eq — the record preimages are the SAME SET, not merely the
-- same measure: arenaRecord is a cylinder over the pointer, so horizontal motion is invisible
-- to it. Landing and both Born bounds then transport with NO measure-theoretic work.
-- ★ IsJointLift.weights_conserved — the weight field is a constant of motion; this is exactly
-- what the Poisson argument {w_i,w_j} = 0 delivers, and it is well-formed only since B1 made
-- the weights C^infinity.
-- ★ IsJointLift.moment_marginal_unchanged — THE HONEST REPLACEMENT for the no-collapse
-- theorem: under a genuine lift the base point moves inside its moment fibre, so
-- pointerEvolve_base_marginal_unchanged FAILS; what survives is that the moment-and-register
-- data is unchanged. Prose about the joint flow must claim this, not the stronger statement.
-- isJointLift_pointerEvolve — non-vacuity (the fibrewise witness is a lift with zero
-- back-reaction). CONDITIONAL by design (CONVENTIONS 8.3 _of_): discharging the hypotheses
-- for the actual X_H is the paper's job, and the Hamiltonian identification stays 2a-scoped.
/-- info: 'CSD.RecordLayer.IsJointLift.outcomeSector_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.IsJointLift.outcomeSector_eq

/-- info: 'CSD.RecordLayer.IsJointLift.weights_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.IsJointLift.weights_conserved

/-- info: 'CSD.RecordLayer.IsJointLift.moment_marginal_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.IsJointLift.moment_marginal_unchanged

/-- info: 'CSD.RecordLayer.jointFlowTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.jointFlowTransfer

/-- info: 'CSD.RecordLayer.isJointLift_pointerEvolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.isJointLift_pointerEvolve

-- ChartBracket (2026-08-04, SigmaLayer/ChartBracket.lean; BACKLOG A3 -- the formalisable
-- fragment of the joint-arena Poisson argument). Stating {w_i,w_j}=0 on the ARENA needs
-- omega^-1 dH, the one arrow Mathlib lacks. In a DARBOUX CHART it is a computation: the
-- bracket is an explicit fderiv expression and the Hamiltonian field is the explicit
-- swap-and-negate (no omega^-1 needed in canonical coordinates).
-- ★ poissonBracket_eq_zero_of_disjoint — the FAITHFUL statement, and NOT the naive one:
-- H = sum_j w_j(x) h_j(q) is NOT momentum-free (it depends on the pointer's momenta), so
-- "both momentum-independent" would be false of H. What holds is DISJOINT SUPPORT: w is
-- momentum-free and its position indices are disjoint from H's momentum indices -- which is
-- exactly the product structure of the arena (base vs pointer).
-- poissonBracket_comm_of_momentumIndep — the easy case {w_i,w_j}=0, no support hypothesis.
-- ★ conserved_of_bracket_eq_zero / weight_conserved_of_disjoint — vanishing bracket implies
-- constant along any integral curve of X_H: the conservation A2 needs, feeding A1's
-- IsJointLift.weights_conserved.
-- SCOPE: a chart MODEL. KSigma x CP^K is not globally R^{2n} and nothing here transports to
-- the arena -- that transport IS the missing arrow (A4). d-omega = 0 is not stated because in
-- a canonical chart it is automatic, which is precisely why this is weaker than the manifold
-- statement.
/-- info: 'CSD.SigmaLayer.poissonBracket_eq_zero_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.poissonBracket_eq_zero_of_disjoint

/-- info: 'CSD.SigmaLayer.poissonBracket_comm_of_momentumIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.poissonBracket_comm_of_momentumIndep

/-- info: 'CSD.SigmaLayer.conserved_of_bracket_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.conserved_of_bracket_eq_zero

/-- info: 'CSD.SigmaLayer.weight_conserved_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.SigmaLayer.weight_conserved_of_disjoint

-- NullSeamLift (2026-08-04, SigmaLayer/NullSeamLift.lean; BACKLOG B2). The third horn was
-- built on S^1 x CP^2 -- real dimension 5, ODD, hence no symplectic structure, which is why
-- its measure had to be renamed nullSeamMeasure. Giving the register its CONJUGATE coordinate
-- makes the arena T^2 x CP^2, dimension 6. The construction is unchanged (the crossing still
-- reads theta_1; theta_2 rides along untouched, as a conjugate variable does when the
-- generator does not depend on it), so every transfer is a cylinder argument.
-- ★★ nullSeamLiftClosure — the third horn on an even-dimensional arena; ★ born_left/right
-- exact r and 1-r via Measure.prod_prod; seam still null (two points x T^1).
-- EARNED: the parity obstruction is gone. NOT EARNED and not claimed: the symplectic FORM
-- itself -- Mathlib has no symplectic API, so "this measure IS the Liouville volume of
-- omega^3/3!" stays section-2a scoped (A4). Even dimension is necessary, not sufficient.
/-- info: 'CSD.RecordLayer.nullSeamLiftClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeamLiftClosure

/-- info: 'CSD.RecordLayer.nullSeamLift_born_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeamLift_born_left

/-- info: 'CSD.RecordLayer.nullSeamEvolveLift_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.nullSeamEvolveLift_measurePreserving

-- PointerFrequency (2026-08-04, SigmaLayer/PointerFrequency.lean; BACKLOG B3a). The smooth
-- horn proved a SINGLE-SHOT sandwich but never said what an experimenter sees. The exact
-- horns have had the frequency layer since LF1; the smooth horn did not.
-- ★ pointer_born_frequency — i.i.d. trials of the smooth witness's preparation: the relative
-- frequency of outcome j converges a.s., and the limit sits in the eps-window
-- [r_j - 2eps, r_j + 2(N-1)eps] (pointerSectorProb_mem_window carries the ENNReal sandwich
-- across toReal, safe because pointerPrep is a probability measure).
-- Nothing new was needed: LF1's freq_tendsto_of_iid is already generic over (measurable
-- space, probability measure, measurable event) and the smooth witness supplies all three.
-- SCOPE: the limit is BRACKETED, not pinned -- the eps-horn's price; and eps -> 0 sharpens
-- the window only ACROSS witnesses, since each eps is a different propagator.
/-- info: 'CSD.RecordLayer.pointer_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointer_born_frequency

/-- info: 'CSD.RecordLayer.pointerSectorProb_mem_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerSectorProb_mem_window

-- PovmSectorBorn (2026-08-04, SigmaLayer/PovmSectorBorn.lean; BACKLOG B4). Discharges the
-- scope note the 2026-08-04 audit added to PovmDynamics: povm_selector_born was DESCRIBED as
-- "the dynamical POVM Born rule" but measures a SELECTOR FIBRE, not a protocol outcome
-- sector -- the distinction SwapClosure states explicitly.
-- ★★ povm_sector_born — the JOIN PROTOCOL's outcome sector (initial states destined for
-- record i) at the dilated preparation carries exactly <psi, E_i psi>. This is the dynamical
-- statement the prose had claimed. povm_sector_born_canonical: every POVM, via canonicalNaimark.
-- It is a two-line composition of join_sector_born (the protocol-sector spine,
-- preimage_sector_ae + volume_goodTheta) with sum_block_normSq_dilate -- which is itself the
-- evidence that the original defect was one of DESCRIPTION, not missing mathematics.
-- Unchanged scope: the instrument stays dilation-relative, and V-as-unitary-stroke is still
-- a recorded extension; both statements take the dilated ray [V psi] as entry point.
/-- info: 'CSD.RecordLayer.povm_sector_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.povm_sector_born

/-- info: 'CSD.RecordLayer.povm_sector_born_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.povm_sector_born_canonical

-- SharpenedNoGo (2026-08-04, SigmaLayer/SharpenedNoGo.lean; BACKLOG B5, the trilemma's
-- third leg -- SHARPENED, NOT CLOSED).
-- ★ posMeasure_noRecord_of_isOpenMap — an OPEN-MAP propagator on an OPEN ready set cannot
-- hide the no-record set in a null set: the image is an open neighbourhood, and any
-- neighbourhood of a boundary point of the no-record set meets its INTERIOR, which has
-- positive measure. posMeasure_noRecord_unitary specialises to a unitary stroke on CP^K
-- (a homeomorphism; FS is positive on nonempty opens). This is exactly why a DIRAC
-- calibration escapes: a point has no neighbourhood to spare, which is how the null-seam
-- witness threads the kissing state and keeps its seam null.
-- ⚠️ WHAT IT DOES NOT PROVE, and a correction to my own earlier claim: NullSeamWitness said
-- a positive-width ready region fattens the seam "of order the calibration width". The ORDER
-- is quantitative, does NOT follow from this topological argument, and is proved nowhere --
-- corrected at source. Also: the forcing step (that some ready state MUST land in the
-- closure of the no-record interior) is a HYPOTHESIS here, not a conclusion; deriving it
-- needs no_everywhere_correlation's connectedness plus a regularity condition on the
-- no-record set. Hence: the leg is sharpened, not closed.
/-- info: 'CSD.RecordLayer.posMeasure_noRecord_of_isOpenMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.posMeasure_noRecord_of_isOpenMap

/-- info: 'CSD.RecordLayer.posMeasure_noRecord_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.posMeasure_noRecord_unitary

-- FORCING STEP CLOSED (same session): exists_noRecord_of_meets_two inverts
-- no_everywhere_correlation -- instead of assuming the image is covered by two record
-- regions and deriving False, conclude it is NOT covered, so a correlating propagator on a
-- preconnected ready set MUST carry some state outside every record region.
-- ★★ posMeasure_noRecord_of_correlates chains that to the measure bound. The hypotheses now
-- split by KIND: everything about the DYNAMICS is discharged (continuity, open map,
-- correlation), and the single remaining assumption is about the RECORD GEOMETRY -- that the
-- no-record set is contained in the closure of its interior. True of the corpus's moment
-- regions (perturb toward the ready vertex) but NOT constructed, so the leg is closed modulo
-- a geometric fact rather than closed outright.
-- [2026-08-05: that geometric fact IS now constructed -- NoRecordGeometry block below;
-- the "closed modulo" qualifier above is superseded and B5 is closed outright.]
/-- info: 'CSD.RecordLayer.exists_noRecord_of_meets_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.exists_noRecord_of_meets_two

/-- info: 'CSD.RecordLayer.posMeasure_noRecord_of_correlates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.posMeasure_noRecord_of_correlates

-- PointerLuders (2026-08-05, SigmaLayer/PointerLuders.lean; BACKLOG B3b, BRICK 1 ONLY).
-- The smooth witness PROVABLY does not collapse (pointerEvolve_base_marginal_unchanged) --
-- a feature, but it means the smooth horn gives records and Born and no state update.
-- Composing with relocation needs an arena carrying pointer AND bank, and a relocation
-- triggered by the POINTER's record region rather than a torus arc. That is this brick.
-- pointerIndex — the readout off the record regions, well defined by their disjointness.
-- pointerRelocate — swap system with bank slot j when the pointer displays j; ★ it never
-- moves the pointer, so the record survives its own relocation.
-- ★ pointerBankSwap_measurePreserving — the slot swap preserves the composed arena measure
-- (same conjugation as the torus version; FS vs Haar plays no part).
-- pointerLudersStroke — the two-stroke composite, DEFINED.
-- ⚠️ NOT PROVED HERE, and the docstring says so: measure preservation of pointerRelocate
-- ITSELF (a piecewise map -- needs the partition argument swapG uses, with record cylinders
-- in place of register arcs), and the conditioned post-measurement marginal. Those are
-- brick 2, and until they land this module is the ARENA AND DYNAMICS, not a Lüders theorem.
-- Nothing here weakens pointerEvolve_base_marginal_unchanged: relocation is a SECOND stroke.
/-- info: 'CSD.RecordLayer.pointerBankSwap_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerBankSwap_measurePreserving

/-- info: 'CSD.RecordLayer.pointerRelocate_pointer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerRelocate_pointer

/-- info: 'CSD.RecordLayer.pointerIndex_eq_some_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.pointerIndex_eq_some_of_mem

-- NoRecordGeometry (2026-08-05, SigmaLayer/NoRecordGeometry.lean; BACKLOG B5-geom -- and
-- with it B5 CLOSED OUTRIGHT).
-- The single remaining hypothesis of the trilemma's third leg was GEOMETRIC: that the
-- no-record set is contained in the closure of its interior. The construction: feed weight
-- into the ready component (feedReady) -- every record numerator is fixed, the norm
-- strictly grows, so every record moment strictly drops below 1/2; the family is
-- phase-preserving on the nonzero branch, so convergence back to the ray is immediate and
-- needs no chart argument.
-- ★ noRecord_subset_closure_strict — the core, for an arbitrary index set of record
-- moments (one proof serves the all-j and pair consumers).
-- ★ noRecord_subset_closure_interior — B5-geom as stated in the BACKLOG row.
-- ★ recordRegion_pair_compl_regular — the pair form posMeasure_noRecord_of_correlates's
-- hreg consumes.
-- ★★ posMeasure_noRecord_pointer — B5: on the pointer manifold, a continuous open-map
-- propagator correlating two outcomes on an open preconnected ready set gives the
-- no-record set positive FS measure. NO geometric hypothesis remains -- exact-a.e. records
-- force Dirac calibration as a THEOREM. Honest scope unchanged: this is the LOCAL leg
-- (the pointer's moment regions); general exhaustiveness over all arenas stays research.
/-- info: 'CSD.RecordLayer.noRecord_subset_closure_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.noRecord_subset_closure_strict

/-- info: 'CSD.RecordLayer.noRecord_subset_closure_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.noRecord_subset_closure_interior

/-- info: 'CSD.RecordLayer.recordRegion_pair_compl_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.recordRegion_pair_compl_regular

/-- info: 'CSD.RecordLayer.posMeasure_noRecord_pointer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.RecordLayer.posMeasure_noRecord_pointer

end CSD.Tests.AxiomAudit
