import CsdLean4.Mathlib.Analysis.Normed.Lp.Matrix
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
import CsdLean4.Mathlib.Topology.Algebra.Module.LinearMap
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
import CsdLean4.LF2.PhaseInvariance
import CsdLean4.LF2.EffectFn
import CsdLean4.LF2.Preparation
import CsdLean4.LF2.Interface
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
import CsdLean4.LF3.Singlet.Leakage
import CsdLean4.LF3.ContextMap
import CsdLean4.LF3.SingletProjective
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF3.Interface
import CsdLean4.Empirical.QM.Bell
import CsdLean4.Empirical.QM.NoCloning
import CsdLean4.Empirical.QM.Multipartite.GHZ
import CsdLean4.Empirical.QM.Contextuality.KS18
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.CSD.Bell
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
