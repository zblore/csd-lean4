# Thermodynamics track — plan

**Status: TH1 DONE 2026-07-05 (EXPECTATION core; concentration/Levy staged as the named
residual); TH2 DONE 2026-07-07 (the H-theorem / second law as pinching entropy monotonicity);
TH3 DONE 2026-07-07 (temperature / free energy / Gibbs variational principle); TH4 DONE 2026-07-07
(Landauer's principle, the Reeb–Wolf bound); TH5 stretch planned.** The thermodynamics track formalises the
statistical-mechanical content that CSD's foundations already imply: Born weights are equilibrium
volume fractions, typicality is forced by the law of large numbers, and the de-isolation flow is
measure-preserving (Liouville). Thermodynamics is the native language of that structure, not a
bolt-on.

## Conceptual frame (CSD alignment)

- **Fine-grained = reversible, measure-preserving.** `μ_L` (Liouville) and the FS-measure-preserving
  de-isolation flows `Φ` are entropy-conserving at the microscopic level (Liouville's theorem, the
  `hΦ_pres` field).
- **Coarse-grained = entropy increase.** Partial trace / pointer-block coarse-graining of a pure
  state produces the von Neumann entropy jump already witnessed at LF6-B.3
  (`decohere_vonNeumann_entropy_pos_of_superposition`, `S: 0 → S > 0`). This is the Boltzmann/Gibbs
  picture: reversible microdynamics, irreversibility from coarse-graining.
- **Typicality = the ensemble.** `μ_FS` is the equilibrium sampling law; Born-from-volume is a
  quantum-equilibrium statement. So CSD's Born rule is structurally a statistical-mechanical
  equilibrium result.
- **CSD-distinctive claim:** thermodynamics EMERGES from the deterministic substrate + typicality; it
  is not postulated. Temperature, free energy, and the second law are derived, not primitive.
- **Finite-sector reading (W4):** real baths are finite, finite-resolution, finite-record; the
  continuum thermodynamic limit is the ideal completion of finite operational sectors.

## Existing corpus support (reuse, do not re-prove)

- `QuantumInfo.vonNeumannEntropy` (K1) + `vonNeumannEntropy_diagonal` + `Real.negMulLog`.
- LF6-B decoherence tier: the pure→mixed entropy-increase witness.
- K2 channels (Kraus/Stinespring/CPTP), K3 trace distance.
- `maxEntangled_marginal_uniform` (LF6-D): the maximally-mixed reduced-state special case.
- The FS measure + typicality machinery (`fubiniStudyMeasure`, LLN via `freq_tendsto_of_iid`,
  `TypicalityForcing`).

## Tranches

### TH1 — canonical typicality (the strongest first tranche)
The Popescu-Short-Winter / Goldstein-Lebowitz-Tumulka-Zanghì statement: for a TYPICAL global pure
state drawn from `μ_FS` on a large system, the reduced state of a small subsystem is close to the
canonical (Gibbs) state; in the equal-energy (unconstrained) case, close to maximally mixed `I/d_S`.
Start with the equal-energy case (microcanonical → maximally mixed), generalising
`maxEntangled_marginal_uniform` from the specific maximally-entangled state to a `μ_FS`-typical state
(concentration of the reduced state near `I/d_S`). This is the natural CSD-thermodynamics bridge:
"thermal equilibrium from volume," directly on the machinery the corpus already has. HONEST scope: a
concentration/typicality result, not a dynamical thermalisation theorem.

**DONE 2026-07-05 (EXPECTATION core), `CsdLean4/Thermo/CanonicalTypicality.lean`.** Landed:
- `fs_first_moment`: `E_{μ_FS}[ |ψ><ψ| ] = (1/N) I` on `ℂℙ^{N-1}` — the FS first moment is maximally
  mixed. A genuine twirl/Schur integral (NOT asserted): entrywise via FS `U(N)`-invariance. Off-diagonal
  entries vanish by a sign-flip diagonal unitary (`signFlip`, `fsFirstMoment_offdiag`: change of
  variables ⟹ `M = -M`); diagonal entries are `1/N` by permutation unitaries + `momentMap_sum_eq_one`
  + `probReal_univ` (`fsFirstMoment_diag`). The diagonal density entry IS `momentMap` (`rayDensity_diag`).
- `canonical_typicality_expectation`: for `H = H_S ⊗ H_E` with `N = d_S·d_E` (reindex equiv `e`),
  `E_{μ_FS}[ Tr_E |ψ><ψ| ] = (1/d_S) I_S`. Partial-traces the FS first moment through the genuine corpus
  `Matrix.traceRight`. The FS-average ANALOGUE of `LF6.maxEntangled_marginal_uniform` (the specific
  maximally-entangled state's marginal) -- an analogy, not a formal Lean dependency (does not cite it).
- HONEST SCOPE: EXPECTATION (average) only. The TYPICAL-state (concentration/Levy) upgrade is the NAMED
  residual (module docstring `Concentration residual`): it needs Levy's lemma / spherical isoperimetry,
  not in Mathlib. No `sorry`/axiom stands in. `fs_first_moment` is exactly the mean Levy would
  concentrate around; only the deviation bound is missing. NOT dynamical thermalisation (needs mixing/ETH).
  CSD-microdynamics reading rests on the shared A5/D1 residue (μ_FS posited as sampling law).
  Foundational-triple; Gleason-free. AxiomAudit-pinned (`fs_first_moment`,
  `canonical_typicality_expectation`).

### TH2 — the second law as coarse-grained entropy monotonicity
Build on LF6-B.3: the fine-grained de-isolation flow is measure-preserving (entropy-conserving), and
coarse-graining (partial trace to a fixed pointer block) is entropy-non-decreasing. Target a general
statement that the coarse-grained von Neumann entropy is monotone under the de-isolation dynamics
(vs the single-step witness LF6-B.3 currently gives). HONEST scope: the H-theorem-style statement for
the specific coarse-graining, not a universal second law.

**DONE 2026-07-07, `CsdLean4/Thermo/SecondLaw.lean`.** Landed:
- `pinch ρ := diagonal (fun i => (ρ i i).re)` — the pointer-basis dephasing / coarse-graining map,
  with `pinch_isHermitian`, trace-preservation on densities, and `pinch_posDef` (Klein support).
- `vonNeumannEntropy_le_pinching` (**the H-theorem**): `S(ρ) ≤ S(pinch ρ)` for a density with
  strictly positive pointer weights. Proof: Klein's inequality `D(ρ‖pinch ρ) ≥ 0` (reusing
  `klein_inequality`) plus the diagonal cross-term identity `Tr(ρ log(pinch ρ)) = Tr(pinch ρ ·
  log(pinch ρ)) = −S(pinch ρ)` — the `cfc log` of the diagonal state is diagonal
  (`cfc_eq_conj_diagonal` at `U = 1`), so the cross term sees only `ρ`'s diagonal.
- `entropy_reversible_then_coarsegrain` (**the second-law statement**): the fine-grained unitary
  step conserves entropy (`vonNeumannEntropy_conj_unitary`, K1) and the following coarse-graining
  does not decrease it, so `S(ρ) = S(UρUᴴ) ≤ S(pinch(UρUᴴ))` — reversible microdynamics, entropy
  from coarse-graining.
- `entropy_production_nonneg`: `S(pinch ρ) − S(ρ) ≥ 0`; its pure-state instance is LF6-B.3
  (`decohere_vonNeumann_entropy_nonneg`).
- HONEST SCOPE: the strict-positivity (Klein support) hypothesis; the H-theorem for a SPECIFIC
  coarse-graining (the pointer-basis pinch), not a universal second law; a statement about the
  coarse-graining map, not dynamical thermalisation. Foundational-triple; Gleason-free.
  AxiomAudit-pinned (`vonNeumannEntropy_le_pinching`, `entropy_reversible_then_coarsegrain`,
  `entropy_production_nonneg`).

### TH3 — temperature and free energy (derived quantities)
Define the Gibbs state as the max-entropy state at fixed mean energy; temperature as the Lagrange
multiplier / `∂S/∂E`; free energy `F = E − TS`. Prove the Gibbs variational principle (Gibbs state
minimises free energy) on finite-dim density operators. Cat-1-adjacent (general QM statistical
mechanics with a CSD-reading docstring).

**DONE 2026-07-07, `CsdLean4/Thermo/FreeEnergy.lean`.** Landed:
- `gibbsState H hH β = exp(-βH)/Z`, built through the Hermitian functional calculus
  `hH.cfc (x ↦ exp(-βx)/Z)`, `Z = partitionFn = ∑ exp(-βλᵢ)`; `gibbsState_posDef` (unitary conjugate
  of the positive diagonal, via `mul_mul_conjTranspose_same`) and `gibbsState_trace = 1` — a genuine
  density.
- `cfc_log_gibbsState` (the crux): `log(ρ_β) = −β·H − (log Z)·1`, both sides `U · diag · Uᴴ` on
  `H`'s eigenbasis (`cfc_eq_conj_diagonal` at the H-diagonalisation), diagonals matched by
  `log(exp(-βλ)/Z) = −βλ − log Z`.
- `freeEnergy H T ρ = Re Tr(ρH) − T·S(ρ)`; `gibbs_free_energy_eq`: `F(ρ_β) = −T log Z`.
- `gibbs_free_energy_min` (**the variational principle**): `F(ρ_β) ≤ F(ρ)` for every density `ρ` at
  `β > 0`. Proof: `β(F(ρ) − F(ρ_β)) = D(ρ ‖ ρ_β) ≥ 0` by Klein's inequality (`relEntropy_nonneg`),
  using the log-linear form of `log ρ_β`.
- HONEST SCOPE: the inequality (not the equality-iff-Gibbs strict case); `[Nonempty n]` (a Gibbs
  state needs ≥1 level); a QM-stat-mech theorem with a CSD reading. Foundational-triple; Gleason-free.
  AxiomAudit-pinned (`gibbs_free_energy_min`, `gibbs_free_energy_eq`, `cfc_log_gibbsState`,
  `gibbsState_posDef`, `gibbsState_trace`).

### TH4 — Landauer's bound (information thermodynamics)
The thermodynamic cost of erasure / measurement: erasing one bit dissipates `≥ kT ln 2`. Connects the
QEC/decoherence tier (measurement = de-isolation = information gain at a thermodynamic cost) to the
second law. Touchpoint already noted in K1.

**DONE 2026-07-07, `CsdLean4/Thermo/Landauer.lean`.** The information-theoretic (Reeb–Wolf) form,
grounded in TH3. Landed:
- `bath_clausius` (the engine): for any bath density `ρ_B'` and the Gibbs state `τ_B`,
  `S(ρ_B') − S(τ_B) ≤ β·(⟨H_B⟩_{ρ_B'} − ⟨H_B⟩_{τ_B})` — the thermodynamic face of
  `D(ρ_B' ‖ τ_B) ≥ 0` (`relEntropy_nonneg`), read through the TH3 Gibbs log identity
  `re_trace_mul_log_gibbs`.
- `landauer_bound` (**the headline**): a system `S` coupled by a global unitary `U` to a bath in the
  Gibbs state obeys `S(ρ_S) − S(ρ_S') ≤ β·ΔQ` (`ΔQ` = heat into the bath). Chain: entropy
  conservation `S(ρ_SB') = S(ρ_S) + S(τ_B)` (`vonNeumannEntropy_conj_unitary` +
  `vonNeumannEntropy_kronecker`) + subadditivity (`vonNeumannEntropy_subadditive`) give
  `S(ρ_S) − S(ρ_S') ≤ S(ρ_B') − S(τ_B)`; `bath_clausius` bounds that by `β·ΔQ`.
- `landauer_one_bit` (**the `kT ln 2`**): erasing a maximally-mixed bit (`S = log 2`) to a definite
  state (`S = 0`) forces `log 2 ≤ β·ΔQ`, i.e. `ΔQ ≥ T log 2 = kT ln 2`.
- HONEST SCOPE: full-rank final marginals + full-rank initial system state (Klein/subadditivity
  support hypotheses; a maximally-mixed bit qualifies); the standard finite-dim Reeb–Wolf setting, a
  genuine bound (not the reversible idealisation). Foundational-triple; Gleason-free. AxiomAudit-pinned
  (`bath_clausius`, `landauer_bound`, `landauer_one_bit`).

### TH5 (stretch) — ETH or a fluctuation theorem
Eigenstate thermalisation (a single energy eigenstate looks thermal on small subsystems) or a
fluctuation theorem (Jarzynski/Crooks). Larger; deferred until TH1-TH3 land.

## Honest residues (carried by the whole track)

- These are QM statistical-mechanics results with a CSD READING; the CSD-distinctive "thermodynamics
  from deterministic dynamics" claim rests on the de-isolation flow being the microdynamics, which is
  the A5/D1 residue shared with all of LF6.
- TH1 is a typicality (concentration) result, not a proof that a given initial state thermalises
  dynamically (that needs mixing / ETH).

## Recommended order

TH1 (canonical typicality) first — highest value, best corpus support, manuscript-strong. Then TH2
(second law), TH3 (temperature/free energy), TH4 (Landauer), TH5 stretch.
