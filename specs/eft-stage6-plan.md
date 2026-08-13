# EFT Stage 6 plan: the cone's consequences

Status: **COMPLETE (2026-08-13, same day)** — CV-20, CV-21, CV-22 all landed;
CV-22's gate ran and PASSED at the sanctioned pattern-resolved scope. Owner queue: `specs/BACKLOG.md` §Q (Q7) and the §CV chain row; ref-tagged
rows in [`future-work.md`](future-work.md).

## Where Stage 5 left the chain

Stage 5 closed with the textbook Lieb–Robinson shape
(`norm_commutator_spatial_factorial_le`: `‖[A(t),B]‖ ≤ 2‖A‖‖B‖(2‖S‖t)^d/d!`)
and two recorded non-claims: **no velocity constant extracted**, and the
continuum posture deliberately deferred (`ApproxCCR.no_exact_finite_ccr`).
Stage 4 left the **channel-level RG** re-scoped as unqueued research after the
`exists_unitary_compress_not_unitary` no-go. Stage 6 takes the cone's
*consequences* — the quantities the record layer actually reads — rather than
reopening either deferred posture.

## Rows

| # | Item | Deps | Size | Status |
|---|---|---|---|---|
| ~~CV-20~~ | ★★★ **The Lieb–Robinson velocity.** Extract an explicit velocity from the Stage-5 factorial bound: outside the cone `v·t ≤ d` with `v = 2e²‖S‖`, the commutator is exponentially small in the graph distance, `‖[A(t),B]‖ ≤ 2‖A‖‖B‖e^{−d}`. | CV-19 | M | **DONE 2026-08-13** (`CV/LiebRobinson.lean`): `pow_pow_le_exp_mul_factorial` (`d^d ≤ e^d·d!`, one term of the exponential series) + `pow_div_factorial_le_exp_neg` (the series term dies exponentially outside `x ≤ d/e²`) + ★★★ `norm_commutator_velocity_le`. **No optimality of the constant is claimed** — `2e²‖S‖` is what the factorial bound yields with the crude `d! ≥ (d/e)^d`; sharpening is possible but not queued. |
| ~~CV-21~~ | ★★ **Vacuum clustering at the cutoff.** | Stage 1, CV-8 | M | **DONE 2026-08-13** (`CV/Propagator.lean`): landed stronger than planned — `diag_entry_mul_of_disjointSupport` factorises the diagonal entry at **any** configuration (unique-intermediate argument, no product-state machinery needed), `vacuum_clustering` instantiates at `vacCfg`. |
| ~~CV-22~~ | **Wick's four-point theorem at the cutoff.** | CV-13 | L, **GATED** | **PASS RUN 2026-08-13; landed pattern-resolved** (`CV/Propagator.lean`): the walk-collapse idiom stayed `fin_cases`-free as required. `eqFourPoint` with the complete coincidence-pattern table — ★★ `eqFourPoint_same` (`= 3/4`, three pairings, needs `2 < N`: at `N = 2` the value is `1/4` — truncation honesty), ★★ `eqFourPoint_pair`/`_alt`/`_outer` (`= 1/4`, the one surviving pairing, needs only `1 < N`), `eqFourPoint_single₁`–`₄` (a mode appearing once kills the expectation — all the vanishing patterns, since every 4-pattern without a singleton is all-equal or two-pairs). These are exactly Wick's `Σ_pairings ∏ ½δ`. Recorded residues (not queued): the packaged single-formula `δ`-sum (assembly, not mathematics); the time-separated four-point (Heisenberg-evolved factors); higher `2n`-point Wick. |

## Non-goals (Stage 6)

- **No continuum limit** — the `ApproxCCR.no_exact_finite_ccr` posture stands.
- **No RG reopening** — the channel-level RG stays unqueued research (Stage 4 record).
- **No velocity optimality** — CV-20's constant is what the factorial bound gives.

Cross-references: `specs/BACKLOG.md` (§Q Q7, §CV chain row);
[`eft-stage5-plan.md`](eft-stage5-plan.md) (the Stage-5 record this continues);
`specs/future-work.md` (CV-20..CV-22 rows).
