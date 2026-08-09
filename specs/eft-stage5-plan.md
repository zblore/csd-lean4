# EFT Stage 5 plan: Lieb–Robinson bounds

Status: PLAN (2026-08-09). Owner queue: `specs/BACKLOG.md` §CV chain row; ref-tagged rows
CV-17..CV-19 in [`future-work.md`](future-work.md). Predecessor:
[`eft-stage4-plan.md`](eft-stage4-plan.md) (Stage 4, complete). Promoted from non-goal to
headline by the Stage-4 horizon note (author-confirmed 2026-08-09).

## What this is, and why it is worth doing

A **Lieb–Robinson bound** is the theorem that non-relativistic lattice quantum dynamics has
an emergent light cone: for observables `A` on region `X` and `B` on region `Y`,

  `‖[A(t), B]‖ ≤ C ‖A‖ ‖B‖ · e^{-μ(d(X,Y) − v|t|)}`

— information leaks outside the cone `d ≤ v|t|` only exponentially. It is the foundation of
essentially all rigorous lattice-QFT/many-body locality results (area laws, exponential
clustering, quasi-adiabatic continuation).

**To our knowledge it has never been formalized in any proof assistant.** It is also not
Mathlib-blocked: the objects are finite matrices, the analysis is the mean-value inequality
and Grönwall, both of which the corpus and Mathlib already have. Stage 4 built its exact
prerequisites: CV-11's exp-closure and the exact kicked cone, CV-12's Trotter/telescoping,
CV-9's Duhamel price, and CV-8's disjoint-support commutation (which supplies the initial
condition `[A, B] = 0` for free).

## The proof strategy (Nachtergaele–Sims form)

With `H` Hermitian, write `τ_t(A) = e^{itH} A e^{-itH}`, and fix `A` supported on `X`, `B`
on `Y`, `X ∩ Y = ∅`. Let `H_X` be the part of the Hamiltonian supported inside `X`, and
`W = H − H_X` the boundary terms.

1. `f(t) := [τ_t(A), B]` satisfies `f'(t) = i[H_X, f(t)] + i[[W, τ_t(A)], B]` — the first
   term because `H_X` commutes with `B` (disjoint supports) so the Jacobi identity collapses
   it into a conjugation.
2. Conjugating it away, `g(t) := e^{-itH_X} f(t) e^{itH_X}` has `‖g(t)‖ = ‖f(t)‖`, `g(0) = 0`
   (CV-8), and `‖g'(t)‖ ≤ 4‖W‖‖A‖‖B‖`.
3. The mean-value inequality then gives the **linear bound** `‖[τ_t(A), B]‖ ≤ 4|t|‖W‖‖A‖‖B‖`.
4. **Iterating** step 3 along chains of overlapping interaction terms, and counting the paths
   from `X` to `Y`, converts the linear bound into the exponential/velocity form.

Steps 1–3 are the corpus's existing `DuhamelBound` pattern (interpolant + mean-value
inequality, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`). **Step 4 is the research
content** and is where every formalization difficulty lives.

## Brick ladder

| Brick | Content | Effort |
|---|---|---|
| **CV-17** — the commutator flow | `CV/LiebRobinson.lean`: `heisenbergFlow H t A := exp(itH) A exp(−itH)` for Hermitian `H`; `norm_heisenbergFlow` (unitary conjugation preserves the L2 operator norm — CV-9's `heisenberg_dist_le` machinery); ★ `hasDerivAt_heisenbergFlow` — `d/dt τ_t(A) = i[H, τ_t(A)]` (from `hasDerivAt_exp_smul_const`, product rule, as in `DuhamelBound`). | **M** |
| **CV-18** — ★★ the linear bound (**the deliverable**) | The interaction-picture split: `commutator_deriv_split` (Jacobi + `H_X` commutes with `B`), the conjugated interpolant `g`, and ★★ `norm_commutator_heisenbergFlow_le`: `‖[τ_t(A), B]‖ ≤ 4|t|·‖H − H_X‖·‖A‖·‖B‖` for disjointly supported `A, B`, with `[A,B] = 0` supplied by CV-8. **Physics content: no instantaneous signalling, quantitatively — the commutator can grow no faster than linearly, at a rate set by the boundary coupling alone.** Instantiate on the CV field: `H_X` = the terms inside `X`, `W` = the edges crossing the cut, so the rate is the cut's coupling strength (`CV/SupportSpreading.lean`'s graph language). | **M/L** |
| **CV-19** — the exponential/velocity form (**GATED, research**) | Iterate CV-18 over chains of overlapping interaction terms; bound the number of length-`n` paths from `X` to `Y` by the coupling graph's branching; resum to `e^{−μ(d − v\|t\|)}` with `v` explicit in the coupling strength and branching. Needs: a path-counting combinatorial lemma, an `n`-fold iterated integral bound (Mathlib's Grönwall `norm_le_gronwallBound_of_norm_deriv_right_le` is the natural engine), and the series resummation. **Do not start without a fresh feasibility pass on the iteration step specifically.** | **XL, research** |

## ⚠️ Honest feasibility verdict (the part that matters)

- **CV-17 + CV-18 are tractable now.** Every ingredient is in the corpus or Mathlib: the
  derivative of a matrix exponential, unitary-invariance of the L2 operator norm, the
  mean-value inequality in the exact shape `DuhamelBound` already uses, and CV-8 for the
  initial condition. Estimated M and M/L. **The linear bound is a real theorem with real
  physics content on its own** — it is the quantitative statement that a lattice theory has
  no instantaneous signalling — and it is worth landing whether or not CV-19 ever does.
- **CV-19 is genuinely research-grade and may not land.** The iteration/path-counting step is
  where published proofs do their work, and formalizing a resummed series over lattice paths
  is materially harder than anything in Stages 3–4. Two specific risks: (i) the iterated
  integral bookkeeping may need an induction over a family of time-ordered integrals that
  Mathlib does not package; (ii) the combinatorial path bound needs a graph-distance
  formalism the corpus has only in `Finset`-neighbourhood form (`graphBall`).
- **Abort criterion, agreed in advance:** if CV-19's feasibility pass does not produce a
  concrete route for the iteration step within one focused session, the stage stops at CV-18
  with the exponential form recorded as an open frontier. Landing CV-18 and stopping is a
  success, not a failure — that is the point of gating.

## Non-goals (unchanged from Stage 4)

No continuum limit (`ApproxCCR.no_exact_finite_ccr` stands); no infinite-dimensional QFT; no
RG flow (CV-16 re-scoped that to a channel-level statement with an error budget); no claim
that the velocity `v` obtained is optimal (Lieb–Robinson velocities are famously not tight).

## Gates and discipline

As every stage: layer-part builds, pins in `Tests/AxiomAudit/Extensions.lean` (`CSD.CV`) or
`MathlibStaging.lean` (staged bricks), foundational-triple isolation checks before pinning,
root wiring + coverage, `check-claims` inventories for new honest-scope phrases, rows struck
on landing, zero-warning build maintained, CI final.

## References

[`eft-stage4-plan.md`](eft-stage4-plan.md) (the horizon note that promoted this);
`CV/SupportSpreading.lean` + `CV/LocalAlgebraClosed.lean` (the exact cones this bound
generalizes); `CV/InteractionPrice.lean` (CV-9); `Mathlib/Analysis/Matrix/DuhamelBound.lean`
(the proof pattern); `Mathlib/Analysis/Matrix/TrotterProduct.lean` (CV-12);
Lieb–Robinson (1972); Nachtergaele–Sims, *Lieb–Robinson bounds in quantum many-body physics*
(2010); Hastings, *Locality in quantum systems* (2010).
