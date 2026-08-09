# EFT Stage 4 plan: dynamics completed, observables, and the covariance seam

Status: **COMPLETE (2026-08-09, same day)** — CV-11..CV-15 landed as planned; CV-16's gate did its job and **changed the statement** (its feasibility pass proved the planned form unattainable: decimation of a support-spreading unitary is not unitary, so the effective theory is necessarily open — positive matching half + no-go landed, the RG proper re-scoped to a channel-level statement with an error budget, recorded unqueued). Kept as the design record. Deltas from the sketch are noted in the struck rows of [`future-work.md`](future-work.md); the Stage-5 horizon note below stands, with both prerequisites now landed. Original status line: PLAN (2026-08-09). Owner queue: `specs/BACKLOG.md` §CV chain row; ref-tagged rows
CV-11..CV-16 in [`future-work.md`](future-work.md). Nothing below is claimed until its row
is struck. Predecessor: [`cv-stage3-plan.md`](cv-stage3-plan.md) (Stage 3, complete).

## Goal and posture

Stage 3 closed the *interaction* clause of the EFT chain. What separates the current corpus
from an honest finite-cutoff EFT is threefold: the dynamics story covers only **diagonal**
interactions (real field theories have hopping/derivative couplings); there is **no
observables tier** (EFT's empirical content is correlation functions, and the chain computes
none); and the **Lorentz content** is carried implicitly by the dispersion's shape rather
than stated. Stage 4 closes those three, plus two cheap complements, and gates the genuine
RG question behind a decision point exactly as Stage 3 gated power counting.

The posture is unchanged: everything at a finite cutoff, no continuum claims
(`ApproxCCR.no_exact_finite_ccr` stands), statements chosen so they survive the limit as
the standard axioms. Non-goals restated at the end.

The physics content, one line each:

1. locality extends to **non-diagonal** couplings — the light cone covers kicked drives
   with arbitrary local kicks (CV-11);
2. arbitrary Hermitian interactions get **constructible** dynamics, not just priced
   distance — Trotter (CV-12);
3. the chain **computes a propagator**: the free two-point function oscillates at the
   dispersion frequency, interacting corrections priced (CV-13);
4. the mass shell is **boost-invariant as a theorem**, not a reading (CV-14);
5. the renormalization-**trivial** class is named: density couplings are cutoff-independent
   on fixed configurations (CV-15);
6. genuine RG matching between cutoffs is a **research decision point** (CV-16).

## What already exists (verified 2026-08-09)

- `CV/LocalAlgebra.lean` — `SupportedOn` closed under `one/add/smul/mul/star/mono`: the
  local algebra. **The subalgebra is a linear subspace of a finite-dimensional matrix
  algebra, hence topologically closed** — the fact CV-11 leans on.
- `CV/SupportSpreading.lean` — `heisenberg_supportedOn_union` (conjugation by ANY
  `T`-supported *unitary* spreads at most onto `S ∪ T`), `heisenberg_eq_of_disjoint`,
  `graphBall`, the diagonal light cone.
- `CV/DynamicalLocality.lean` — `heisenberg_phaseDiagU_apply`: the evolved-entry formula
  the propagator computation reads off.
- `CV/Dispersion.lean` — exact `ω(m,p) = √(p² + m²)`, `omega_sq_sub_sq` (mass shell),
  `abs_le_omega`, mass gap; `relFieldHamiltonian` (diagonal, relativistic eigenvalues).
- `CV/InteractionPrice.lean` + `EchoBound.lean` — the Duhamel price and the telescoping
  `‖Uⁿψ − Wⁿψ‖ ≤ n‖U−W‖‖ψ‖`; the matrix-level power bound `‖Uⁿ − Wⁿ‖ ≤ n‖U−W‖` is the
  same telescoping, a small lemma away.
- `CV/OscillatorBorn.lean` — `embedMode` and the `_cutoff_independent` lineage
  (`oscEnergy`, `fieldEnergy`, `numberBornProb_embed`) that CV-15 extends.
- Mathlib at pin: `exp` series API (`NormedSpace.exp_eq_tsum`), closed-submodule limit
  membership (`Submodule.closedComplemented`/finite-dim closedness + `IsClosed.mem_of_tendsto`),
  `Real.cosh_sq_sub_sinh_sq`.

## Brick ladder

| Brick | Content | Effort |
|---|---|---|
| **CV-11** — the non-diagonal light cone | `CV/LocalAlgebraClosed.lean` (or extend `LocalAlgebra`): package `SupportedOn T` as `localAlgebra T : Subalgebra ℂ (Matrix …)` from the proved closure lemmas; prove the carrier **topologically closed** (a linear subspace of a finite-dim space — `offDiag`/`indep` are closed conditions, or route through `Submodule` + finite-dim closedness); ★ `exp_mem_localAlgebra` — `exp` of a `T`-supported matrix is `T`-supported (partial sums stay in the algebra; limit membership by closedness). Then `CV/SupportSpreading` extension: a **kicked drive** `freeFieldU · exp(-(iλ)•V₁) · … · exp(-(iλ)•Vₘ)` with each `Vᵢ` supported on an edge gets the same `graphBall` light cone — with **arbitrary (non-diagonal, hopping) kicks**, via `heisenberg_supportedOn_union` + CV-6's free-part invariance. ⚠️ Honest split: this covers *kicked* drives. The light cone for the **full** `exp(-(iτ)(H_free + V))` with non-commuting non-diagonal `V` is genuine Lieb–Robinson (velocity bounds from commutator norms) — recorded as the frontier beyond this brick, not attempted. | **M** |
| **CV-12** — matrix Lie–Trotter | Staging brick (`CsdLean4/Mathlib/Analysis/Matrix/TrotterProduct.lean`, `upstream-candidate(mathlib)`, L2Operator scope): `‖(exp(A/n)·exp(B/n))ⁿ − exp(A+B)‖ → 0`, skew-Hermitian case first (all factors unitary, so the telescoping has no growth factors — same structure as the Duhamel proof). **Pivot to check first**: a quantitative second-order exp remainder (`‖exp X − 1 − X‖ ≤ ‖X‖²·e^{‖X‖}`-class) at the pin; if absent it is itself a small series-bound brick. Payoff: the interacting drive for ANY Hermitian `V` becomes a *limit of constructible steps*, closing the "no closed-form step" caveat that CV-7 and the map carry. | **M/L** |
| **CV-13** — the finite free propagator | `CV/Propagator.lean`: `vacuumState` (the all-zero configuration basis vector); the two-point function `freeTwoPoint k l n := ⟨vac, Q_k(n) · Q_l · vac⟩` with `Q_k(n)` the CV-6 Heisenberg evolution under the free (or relativistic, `relFieldHamiltonian`) drive. ★★ `freeTwoPoint_eq`: explicitly `(1/2)·e^{-i n τ ω(m, p_k)}·δ_{kl}` — **the lattice propagator, oscillating at the dispersion frequency**: the chain's first computed correlation function, with `ω(m,p)` appearing as an observable time-dependence rather than a spectrum label. Route: `Q_l·vac` is a single-excitation state; the diagonal drive contributes the phase difference `e^{-inτ(E_exc − E_vac)} = e^{-inτω}` via `heisenberg_phaseDiagU_apply`; orthogonality kills `k ≠ l`. Then ★ `twoPoint_interacting_dist_le`: the interacting two-point function stays within `2nτ·|λ|·C·‖Q_k‖‖Q_l‖`-class of the free one (matrix power bound `‖Uⁿ−Wⁿ‖ ≤ n‖U−W‖` + `|⟨ψ,(A−B)ψ⟩| ≤ ‖A−B‖` + CV-9/CV-10 norm bricks) — the Born-approximation error, priced. | **M** |
| **CV-14** — boost covariance of the mass shell | `CV/Boost.lean`: the 1+1D boost `(ω,p) ↦ (ω·cosh χ − p·sinh χ, p·cosh χ − ω·sinh χ)`; ★ `boost_mass_shell` — `(ω')² − (p')² = ω² − p²` (pure algebra, `cosh² − sinh² = 1`), so the boosted dispersion satisfies the same shell: **the Lorentz content of `CV/Dispersion` as a theorem**; `boost_forward` — the forward shell (`0 < ω`) is preserved (uses `abs_le_omega` + the mass gap). Honest scope: one-particle kinematic covariance at the dispersion level; no claim of a boost action on the mode lattice (which breaks it) — that asymmetry is the standard cutoff honesty, stated. | **S/M** |
| **CV-15** — the renormalization-trivial class | Extend the `_cutoff_independent` lineage: occupation-defined potentials (`densityCoupling` with a cutoff-uniform `g : ℕ → ℕ → ℝ` restricted per cutoff) have cutoff-independent values on embedded configurations, hence the diagonal interacting drive's matrix elements between fixed low configurations are **equal across cutoffs at equal couplings** (`interactingU_cutoff_independent`) — the "relevant side" complement CV-10's doc names: **this operator class needs no renormalization**, as a theorem. | **S/M** |
| **CV-16** — RG matching (DECISION POINT) | The genuine renormalization question: a decimation/coarse-graining map from the cutoff-`N'` theory to cutoff-`N`, and couplings `λ(N')` chosen so low-energy observables agree. For diagonal drives CV-15 makes matching trivial; the nontrivial content requires non-diagonal interactions, i.e. **gated on CV-12**, and a fresh feasibility pass before anyone commits (the CV-10 discipline). Do not start from this plan. | **L/XL, gated** |

Ordering rule (inherited): build only the interface needed to state each ★, then prove it.
Recommended cut: **CV-11 + CV-12 together** (the dynamics completion), then **CV-13** (the
payoff), then CV-14/CV-15 as cheap closers, then the CV-16 gate.

## ⚠️ Honest scope

- **No continuum limit** — `no_exact_finite_ccr` is the standing wall; every statement is
  at finite `(K, N)`, chosen to survive the limit as the standard axiom.
- **No infinite-dimensional QFT** — per the programme's scope ladder; not required.
- **No Lieb–Robinson velocity bounds in Stage 4** — CV-11 covers kicked drives; the
  full-exponential cone is promoted to the Stage-5 headline (horizon note below), gated
  on CV-11 + CV-12.
- **No RG flow claims** — CV-16 is a gated question, not a promise; relevant/irrelevant
  remains, until then, the CV-10 price-bound statement.
- **Covariance is one-particle and kinematic** (CV-14); the lattice breaks Lorentz and the
  plan says so rather than hiding it.

## Stage 5 horizon (recorded intent, author-confirmed 2026-08-09)

**Lieb–Robinson velocity bounds are promoted from non-goal to the Stage-5 headline.** The
light cone for the full `exp(-(iτ)(H_free + V))` — commutators exponentially small outside
an effective cone, rather than exactly zero inside a ball — is genuine research-grade
formalization (to our knowledge unformalized in any proof assistant), it is NOT
Mathlib-blocked (finite matrices, series bounds), and Stage 4 builds its exact
prerequisites: the kicked cone (CV-11) supplies the exact-locality skeleton, Trotter
(CV-12) the approximation bridge, and the quantitative ingredient — per-step support
leakage bounded in norm, summed geometrically — is the actual Lieb–Robinson argument.
The naive route (Trotterize, use the kicked cone per step) provably gives nothing: `n`
Trotter steps grow the exact ball by `n` edges. Stage 5 is gated on CV-11 + CV-12 landing
and a fresh feasibility pass. Not part of Stage 4's claims.

## Gates and discipline (every brick)

Per the standing workflow: layer-part builds locally, pins in the namespace-matching part
(`CSD.CV` → `Tests/AxiomAudit/Extensions.lean`; staging → `MathlibStaging.lean`),
foundational-triple isolation checks before pinning, root wiring + coverage, `check-claims`
inventories for any new honest-scope phrases, rows struck on landing, map updated,
zero-warning build maintained, CI final.

## References

[`cv-stage3-plan.md`](cv-stage3-plan.md) (the predecessor, and the 3b exp-closure sketch
CV-11 executes); [`future-work.md`](future-work.md) rows CV-11..CV-16;
[`external-library-map.md`](external-library-map.md) §H (kicked-model seam);
`CV/{LocalAlgebra,SupportSpreading,Dispersion,InteractionPrice,OscillatorBorn}.lean`;
`Incubator/QuantumChaos/EchoBound.lean`; `specs/BACKLOG.md` §CV chain row.
