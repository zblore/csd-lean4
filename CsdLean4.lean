import CsdLean4.LF1.Setup
import CsdLean4.LF1.Preparation
import CsdLean4.LF1.Outcomes
import CsdLean4.LF1.Trials
import CsdLean4.LF1.Indicators
import CsdLean4.LF1.Expectation
import CsdLean4.LF1.Convergence
import CsdLean4.LF1.MainTheorem
import CsdLean4.LF2.Setup
import CsdLean4.LF2.MeasureBridge
import CsdLean4.LF2.Weights
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.Interface
import CsdLean4.LF3.Setup
import CsdLean4.LF3.Hamiltonian
import CsdLean4.LF3.BranchSeparation
import CsdLean4.LF3.Projectors.Core
import CsdLean4.LF3.Projectors.BranchWeight
import CsdLean4.LF3.Projectors.LF2Interface
import CsdLean4.LF3.Projectors.TensorModel
import CsdLean4.LF3.Singlet.State
import CsdLean4.LF3.Singlet.Expectations
import CsdLean4.LF3.Singlet.Kernel
import CsdLean4.LF3.Singlet.Leakage
import CsdLean4.LF3.ContextMap
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF3.Interface
import CsdLean4.Tests.AxiomAudit
import CsdLean4.Tests.Examples

/-!
# CSD

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
-/
