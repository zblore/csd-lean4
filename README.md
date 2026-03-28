# csd-lean4

Lean4 formalisation of Constraint-Surface Dynamics, beginning with LF1: volume typicality and frequency convergence for deterministic repeated trials.

## Overview

This repository contains the Lean4 development for the finite-dimensional formalisation branch of the Constraint-Surface Dynamics (CSD) programme.

The first target is **LF1**, which formalises the repeated-trial frequency theorem underlying volume-based deterministic accounts of quantum statistics. In this setting, a finite-measure ontic state space is equipped with:

- a measurable preparation region
- a measurable outcome region
- a deterministic measure-preserving flow
- a repeated-trial preparation model

The main goal of LF1 is to show that empirical frequencies converge to the corresponding normalised volume weights under repeated preparation.

LF1 is a frequency theorem. It is **not** a full Born-rule derivation.

## Current scope

The present repository begins with the LF1 layer only.

LF1 formalises:

- the ontic measurable setup
- the preparation probability measure
- measurable outcome events
- repeated trials
- indicator random variables
- the expectation-to-weight bridge
- frequency convergence via a law of large numbers

Later formalisation targets are expected to include:

- **LF2**: measure bridge and Born-weight wrapper
- **LF3**: mixed states, POVMs, and reduction
- **LF4**: control Hamiltonians and outcome basins
- **LF5**: outcome-conditioned update and sequential circuits

## Mathematical target of LF1

For a finite-measure ontic state space \((\Sigma,\mu_L)\), measurable preparation region \(\Omega_0 \subset \Sigma\), measurable outcome region \(\Omega_i^\Sigma\), and deterministic \(\mu_L\)-preserving flow \(\Phi_t\), LF1 studies repeated trials whose initial microstates are sampled independently from the conditional preparation measure on \(\Omega_0\).

For each outcome region, the associated empirical frequency is expected to converge to the corresponding normalised ontic weight.

At the current implementation stage, the formal development is organised so that:

1. the preparation measure is defined explicitly
2. outcome events are pulled back through the deterministic flow
3. indicator random variables are constructed on the repeated-trial sample space
4. convergence is obtained from a law of large numbers
5. the expectation of the indicator is identified with the corresponding ontic weight

## Repository structure

```text
CSD/
  LF1/
    Setup.lean        -- ontic space, μL, Φ, Ω0
    Preparation.lean  -- conditional preparation measure
    Outcomes.lean     -- outcome regions, weights
    Trials.lean       -- TrialModel: i.i.d. repeated-trial probability space
    Indicators.lean   -- indicatorRV, empiricalFreq
    Expectation.lean  -- E[indicator] = weightReal bridge
    Convergence.lean  -- strong law of large numbers application
    MainTheorem.lean  -- LF1 main theorem and corollaries
CSD.lean
```
