# EFT Stage 6 plan: the cone's consequences

Status: **OPENED 2026-08-13** (Q7/E4). CV-20 landed same day; CV-21 queued; CV-22
gated. Owner queue: `specs/BACKLOG.md` §Q (Q7) and the §CV chain row; ref-tagged
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
| CV-21 | ★★ **Vacuum clustering at the cutoff.** The free vacuum is a mode product state, so vacuum expectations of disjointly supported observables factorise: `⟨vac|AB|vac⟩ = ⟨vac|A|vac⟩⟨vac|B|vac⟩` for `SupportedOn R A`, `SupportedOn Y B`, `Disjoint R Y`. The statics companion to the dynamic cone: correlations, like signals, are local at the cutoff. | Stage 1 (`vacuumState`, `norm_sq_tprodState`), CV-8 | M | queued |
| CV-22 | **Wick's four-point theorem at the cutoff.** `⟨vac|Q_k Q_l Q_m Q_n|vac⟩` = the three pairings of `freeTwoPoint`, exact above occupation 4 (the truncation is invisible below the cutoff edge — the honest finite-`N` form). Unlocks perturbative corrections beyond the first-order price. | CV-13 (`freeTwoPoint`) | L, **GATED** | feasibility pass first: the ladder-operator combinatorics at finite `N` must stay `fin_cases`-free; abort to a 2-point-only strengthening if the pairing bookkeeping balloons |

## Non-goals (Stage 6)

- **No continuum limit** — the `ApproxCCR.no_exact_finite_ccr` posture stands.
- **No RG reopening** — the channel-level RG stays unqueued research (Stage 4 record).
- **No velocity optimality** — CV-20's constant is what the factorial bound gives.

Cross-references: `specs/BACKLOG.md` (§Q Q7, §CV chain row);
[`eft-stage5-plan.md`](eft-stage5-plan.md) (the Stage-5 record this continues);
`specs/future-work.md` (CV-20..CV-22 rows).
