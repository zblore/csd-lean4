import CsdLean4.Mathlib.Analysis.Normed.Lp.Matrix
import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvex
import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvexBridge
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Unitary
import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryCompact
import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryHaar
import CsdLean4.Mathlib.LinearAlgebra.Matrix.PartialTrace
import CsdLean4.Mathlib.MeasureTheory.LintegralFintypeProd
import CsdLean4.Mathlib.Probability.IIDCoordinateProcess
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
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularSub
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularConst
import CsdLean4.Mathlib.QuantumInfo.Reversible.Depth
import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop
import CsdLean4.Mathlib.QuantumInfo.Reversible.ProgramRouter
import CsdLean4.Mathlib.QuantumInfo.Reversible.ProgramRouterDoubling
import CsdLean4.Mathlib.QuantumInfo.Reversible.DoublingAssembly
import CsdLean4.Mathlib.QuantumInfo.Reversible.DoublingAssemblyOps
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.AndAdd
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
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
import CsdLean4.Mathlib.Topology.Algebra.Module.LinearMap
import CsdLean4.LF1.Setup
import CsdLean4.LF1.Preparation
import CsdLean4.LF1.Outcomes
import CsdLean4.LF1.Trials
import CsdLean4.LF1.Indicators
import CsdLean4.LF1.Expectation
import CsdLean4.LF1.Convergence
import CsdLean4.LF1.MainTheorem
import CsdLean4.LF1.GeneralFrequency
import CsdLean4.LF2.Setup
import CsdLean4.LF2.MeasureBridge
import CsdLean4.LF2.Weights
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.ReducedDensity
import CsdLean4.LF2.PhaseInvariance
import CsdLean4.LF2.EffectFn
import CsdLean4.LF2.Preparation
import CsdLean4.LF2.Interface
import CsdLean4.LF2.POVM
import CsdLean4.LF2.EffectAux
import CsdLean4.LF3.Setup
import CsdLean4.LF3.Hamiltonian
import CsdLean4.LF3.SectorSeparation
import CsdLean4.LF3.Projectors.Core
import CsdLean4.LF3.Projectors.SectorVolume
import CsdLean4.LF3.Projectors.LF2Interface
import CsdLean4.LF3.Projectors.TensorModel
import CsdLean4.LF3.Singlet.State
import CsdLean4.LF3.Singlet.Expectations
import CsdLean4.LF3.Singlet.Kernel
import CsdLean4.LF3.Singlet.JointProjector
import CsdLean4.LF3.Singlet.JointEig
import CsdLean4.LF3.Singlet.Leakage
import CsdLean4.LF3.ContextMap
import CsdLean4.LF3.SingletProjective
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF3.Interface
import CsdLean4.LF4.Instance
import CsdLean4.LF4.KahlerInstance
import CsdLean4.LF4.KahlerFlow
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
import CsdLean4.LF4.MomentRatioUniformN
import CsdLean4.LF4.MomentRatioUniform
import CsdLean4.LF4.MomentUniform
import CsdLean4.LF4.MomentBridgeN
import CsdLean4.LF4.MomentDirichletN
import CsdLean4.LF4.MomentBornN
import CsdLean4.LF4.BornFrequencyN
import CsdLean4.LF4.QubitConsistency
import CsdLean4.LF4.SingletKahler
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
import CsdLean4.LF4.POVMDilation
import CsdLean4.LF4.POVMVolume
import CsdLean4.LF4.POVMNaimark
import CsdLean4.LF4.BornRegionUncond
import CsdLean4.LF4.BornRegionDisjoint
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
import CsdLean4.LF6.SingletDeisolationFlow
import CsdLean4.LF6.LocalDeisolationFlow
import CsdLean4.LF6.Decoherence
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
import CsdLean4.Empirical.CSD.BellVolume
import CsdLean4.Empirical.CSD.GHZVolume
import CsdLean4.Empirical.CSD.HardyVolume
import CsdLean4.Empirical.CSD.ContextVolume
import CsdLean4.Empirical.CSD.UncertaintyVolume
import CsdLean4.Empirical.CSD.TrineVolume
import CsdLean4.Empirical.CSD.USDVolume
import CsdLean4.Empirical.CSD.SICVolume
import CsdLean4.Empirical.CSD.QutritPOVMVolume
import CsdLean4.Empirical.CSD.SIC3Volume
import CsdLean4.Empirical.CSD.MUB3Volume
import CsdLean4.Empirical.CSD.VolumeCanonical
import CsdLean4.Empirical.CSD.Resources.SuperdenseCoding
import CsdLean4.Empirical.CSD.Resources.Teleportation
import CsdLean4.Empirical.CSD.Crypto.QuantumMoney
import CsdLean4.Empirical.CSD.Crypto.E91
import CsdLean4.Empirical.CSD.QEC.ThreeQubit
import CsdLean4.Empirical.CSD.Contextuality.KS18
import CsdLean4.Empirical.CSD.Contextuality.KS18Volume
import CsdLean4.Empirical.CSD.Contextuality.MerminPeres
import CsdLean4.Empirical.CSD.Contextuality.MerminPeresVolume
import CsdLean4.Empirical.CSD.Hardy
import CsdLean4.Empirical.CSD.Multipartite.GHZ
import CsdLean4.Empirical.QM.Gates.SingleQubit
import CsdLean4.Empirical.QM.Gates.TwoQubit
import CsdLean4.Empirical.QM.Gates.BellPrep
import CsdLean4.Empirical.QM.Gates.MultiQubit
import CsdLean4.Empirical.QM.MeasurementUncompute
import CsdLean4.Empirical.CSD.Gates.Framework
import CsdLean4.Empirical.CSD.Gates.SingleQubit
import CsdLean4.Empirical.CSD.Gates.TwoQubit
import CsdLean4.Empirical.CSD.Gates.BellPrep
import CsdLean4.Empirical.CSD.Gates.MultiQubit
import CsdLean4.Empirical.CSD.Einselection
import CsdLean4.Empirical.Metrology.Ramsey
import CsdLean4.Empirical.Metrology.QuantumFisher
import CsdLean4.Empirical.Metrology.Heisenberg
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
