# Where measurement contextuality lives in Σ — the qubit / general-`N` boundary

> **★ THE HEADLINE FINDING, and the decision that follows from it (updated 2026-07-29).**
> This is the canonical record of the general-`N` contextuality question. **The base-only
> route is PARKED — do not resume it.** Read this section before touching A7. Companions:
> [`record-layer-plan.md`](record-layer-plan.md) (MD-1), [`BACKLOG.md`](BACKLOG.md),
> [`CSD-CHARTER.md`](CSD-CHARTER.md).

## One-line lesson

**The Born rule is an ontic typicality volume for every `N` (a theorem). But *where the
measurement contextuality sits in Σ* is dimension-dependent: it works on the projective base for
the qubit, and at `N ≥ 3` the base-only route is so tightly constrained that the fibre is the
live architecture.** The elegant "regions on the Bloch sphere" picture is a `CP¹ = S²` accident.

⚠️ **Stated precisely, because an earlier version of this line said "necessarily in the fibre"
and an earlier BACKLOG row said "provably dead" — both retracted 2026-07-28.** Base-only A7 at
`N ≥ 3` is **open in both directions**: not proved impossible, not exhibited. What *is* proved is
a chain of necessary conditions (below) that leaves very little room, plus a structural threshold
separating `N = 2` from `N ≥ 3` that shows up three independent ways.

## The derived constraint chain (2026-07-28/29) — what replaced the numerics

Under `U(N)`-covariance a base-only preparation density collapses to `ρ_ψ(φ) = g(|⟨ψ|φ⟩|²)` for a
single non-negative `g`. Everything below constrains that `g`. All Lean, foundational-triple,
axiom-pinned (`SigmaLayer/ContextFixedA7.lean`, `ContextFixedA7FS.lean`).

| # | Result | Content |
|---|---|---|
| 1 | `overlapSupport_ae_subset`, `overlapSupports_ae_disjoint`, `sum_measure_overlapSupport_le_one` | Evaluating A7 at the `n` basis-vector preparations forces each support into its own region; supports pairwise a.e. disjoint; measures sum to `≤ 1`, so each is `≤ 1/n`. **The density must spike.** |
| 2 | `cap_of_joint_nondegenerate` | `g` vanishes a.e. below `½`. **Sharp and attained** — the `N = 2` solution `4(2s−1)₊` is supported exactly on `(½,1]`. |
| 3 | `fs_joint_abundance`, `fs_cap_unconditional` | The cap made **unconditional** at `N ≥ 3` for the actual `μ_FS`, via the corpus's Dirichlet pushforward. |
| 4 | `orthogonal_preparation_vanishes`, `vanishes_on_interval_of_dense` | First **generic-`ψ`** input: `ψ ⊥ eᵢ` also gives zero Born weight, and such `ψ` sweep an interval of overlap values. |
| 5 | `vanishes_below_of_balanced`, `fs_balanced_abundance` | `g` vanishes below `(n−1)/n`. At `n = 2` that reads "below `½`" — again exactly the known solution's support. |

**The `N = 2` vs `N ≥ 3` threshold appears three independent ways**, each exempting the qubit for
the same structural reason:

1. *Two coordinates below `½`* — impossible at `N = 2` where `s₂ = 1 − s₁` is functionally
   dependent (`joint_degenerate_of_sum_eq_one`).
2. *Two distinct free simplex coordinates* — needs `M = N − 1 ≥ 2`.
3. *Tilting `ψ` inside `eᵢ^⊥`* — needs `dim eᵢ^⊥ ≥ 2`.

## Why the chain stopped, and why that is the right call

Two inputs remain undischarged (`hdense`, the tilt fact; and the residual generic-`ψ` gap), and the
terminal step — a harmonic-analysis argument on `ℂℙⁿ⁻¹` — is **blocked on Mathlib infrastructure
that does not exist**. One refutation route is also closed: the natural kill via the Fubini–Study
triangle inequality is *exactly* tight (`arccos√σ + arccos√(1−σ) = π/2`), so it yields nothing. The
constraint system sits **on** the boundary rather than over it.

**The decisive argument for stopping: proving the no-go and assuming it lead to the same next
action.** Either way the fibre carries contextuality at `N ≥ 3`. A constraint chain this tight —
derived theorems, three independent thresholds, independent numerical agreement — falls short of a
formal impossibility result, and that gap matters for a paper claim; it does not change what to
build. So the base-only route is **parked as a well-characterised open problem**, not pursued
further.

*(Note: an earlier phrasing of that sentence tripped `check-claims` (6) by putting a settled-claim
word beside the word "numerics" while explicitly denying the claim. It was reworded rather than
exempted — the co-occurrence rule cannot read contrast, and adding exemptions to silence it would
erode the guard. Documented in the script's KNOWN LIMIT section.)*

## The three-way split (keep these apart)

1. **Born = ontic typicality volume — PROVEN, all `N`, foundational-triple.**
   `LF4/ObservableCorrespondenceN.fsMeasure_bornRegionN`: `|⟨eᵢ|ψ⟩|²` *is* a Fubini–Study
   typicality volume `μ_FS(bornRegionN ψ i)` for every `N`. The central CSD thesis (Born from
   typicality, not a postulate) is not in question — it is a theorem. Empirical adequacy is
   secured independently of everything below.

2. **Base-only, context-fixed measurement — works at `N = 2`, PROVEN.**
   `LF4/QubitBorn.qubitBorn` (the 7-module `CP¹` chain): a genuinely *apparatus-defined*
   partition (the hemispheres `H±(n)`, a function of the measurement axis `n` alone, **not** the
   preparation) weighted by the prep spread density `4(2·blochProj ψ − 1)₊` integrates against
   `μ_FS` to the Born weight `|⟨n|ψ⟩|²`. A7-faithful, on the base, for the qubit.

3. **Base-only, context-fixed measurement — OPEN at `N ≥ 3`, and tightly constrained.**
   ⚠️ **This item read "IMPOSSIBLE" until 2026-08-25.** That wording contradicted the
   retraction recorded in the one-line lesson above (2026-07-28) and was the source of a
   month of downstream drift — it propagated into the published glossary, `docs/PATHS.md`,
   `CSD-CHARTER.md`, `INDEX.md`, `paper-candidates.md` and two Lean docstrings, all of
   which stated the `N ≥ 3` base-only failure as proved. It is not proved.

   The open question is whether there is a `U(N)`-covariant, radial, nonnegative base
   density `g(|⟨ψ|φ⟩|²)` on `ℂℙⁿ⁻¹` with `∫_{Ωᵢ(M)} g dμ_FS = |⟨eᵢ|ψ⟩|²` for the
   max-overlap (Voronoi) cells and all `M, ψ`. The derived constraint chain above is the
   current state of the answer: machine-checked necessary conditions that leave very
   little room, short of a no-go. **Do not restate this as settled in either direction.**
   - **Superseded evidence** (kept for provenance; replaced by the constraint chain, and
     load-bearing for nothing): (a) Phase-1 sampling on `ℂℙ²` — the non-negative
     least-squares fit came back negative on the covariant base density (`r_nn` plateaus
     ~10× the noise floor, stable under 4× samples; the qubit control passes). (b) Operator argument: the affine "dipole"
     `∫_{Ωᵢ}|φ⟩⟨φ|dμ = a·Pᵢ + b(I−Pᵢ)` *does* reproduce Born, but only as a **signed** density;
     restoring nonnegativity needs a monopole rectifier whose per-cell integral is `ψ`-independent
     **only via the qubit antipode `s ↔ 1−s`, `H₊ ↔ H₋`** (a `CP¹ = S²` involution with no `N ≥ 3`
     analogue).

## This is NOT Gleason / Kochen–Specker

Both theorems assume **non-contextuality**. CSD is explicitly **contextual and non-local**, so
neither constrains it. The `N ≥ 3` obstruction above is *not* a no-go theorem — it is **covariance
+ nonnegativity** killing one specific radial base ansatz. (An earlier note that "Gleason forces
the fibre" was a mis-attribution and has been corrected.) Do **not** re-derive the `N ≥ 3` failure
as a Gleason result.

## The resolution: contextuality moves to the fibre (and that is CSD-legit)

`Σ = base × fibre` (`SigmaLayer/FibredSigma`, `KSigma = CPN × T²`). For a sharp preparation the
**base** is pinned at `[ψ]` (= the corpus `push_dirac`), and the **measurement carves the fibre**:
a "Born partition of the fibre" `{Fᵢ(M, φ)}` with `ν(Fᵢ) = |⟨eᵢ|φ⟩|²` (probabilities depend only
on `(eᵢ, φ)` — measurement-noncontextual; the *regions* depend on the full context `M` —
contextual). Phase-2b (2026-07-25) settled **existence**: the softmax / **Gumbel race**
`Fᵢ = argmaxⱼ(log|⟨eⱼ|φ⟩|² + ξⱼ)`, `ξ` i.i.d. Gumbel, reproduces Born *exactly* at `N = 3`
(verified incl. a shared-vector KS check).

**Why this is not "injected noise" that defeats the point:** the fibre is **ontic**, and its
unknown initial value being typicality-distributed is the *same* ignorance-of-initial-condition
that CSD uses everywhere (Born = LLN over the unknown microstate). The context enters through the
**deterministic** comparison map (which basis the argmax runs against), *not* through the fibre
distribution — the fibre law `ξ` is fixed, prep- and measurement-independent. So it is a legitimate
CSD structure: deterministic map + fixed typicality, not an external random oracle.

## Consequence for A7 and for Σ

- **A7 as literally stated** ("epistemic outcome regions `{Ωᵢ(M)} ⊂ ℂℙⁿ⁻¹`") is *established* only
  at `N = 2` (`LF4/QubitBorn.lean`). At `N ≥ 3` it is neither established nor refuted — but the
  constraint chain above leaves so little room that the **fibre** is the architecture to build on.
  This is a substantive revision, not cosmetic; it is also a *decision under uncertainty*, and the
  docs must not restate it as a proved impossibility.
- **What we learned about Σ:** the fibre is not decorative — it is *load-bearing* for measurement
  at `N ≥ 3`. The base `ℂℙⁿ⁻¹` is a lossy epistemic projection; the record-forming, contextual,
  non-local content lives over it in the fibre. This is consistent with (and pressure toward) the
  broader CSD picture where records → spacetime and Σ-locality explains apparent non-locality.

## The genuine open frontier (not a defect — the next research)

The fibre mechanism is currently **posited** (softmax/Gumbel form), not **derived** from a specific
CSD de-isolation dynamics. The open problem: exhibit a de-isolation coupling whose deterministic
flow on `Σ = base × fibre`, with fixed fibre typicality, *yields* the Born-reproducing fibre
partition — i.e. derive the softmax law rather than assume it. This fuses MD-1 (the record layer)
with the "constrain-Σ from above" programme.

## What would actually invalidate CSD (and why we are not there)

Only this: a proof that **no** deterministic-map-plus-typicality structure on any `Σ` can reproduce
Born at `N ≥ 3`. The opposite is established — **existence is settled** (Phase-2b). So these findings
**constrain** CSD's structure (contextuality is fibre-based beyond the qubit) rather than refute it.
They cost the elegant base-region picture and leave a derivation gap; they do not touch empirical
adequacy or the Born-as-typicality theorem.

## Pointers

- **Lean (proven):** `LF4/QubitBorn.lean` (`qubitBorn`, base-only `N=2`);
  `LF4/ObservableCorrespondenceN.lean` (`fsMeasure_bornRegionN`, Born = volume all `N`);
  `LF4/QubitCrossTerm.lean` (the antipode symmetry, `CP¹`-specific).
- **Numerics (not Lean):** `scripts/experiments/record_layer_base_only_test.py` (Phase-1, base-only
  fails `N=3`); `record_layer_fibre_gumbel.py` (Phase-2b, fibre model reproduces Born).
- **Lean (the constraint chain, 2026-07-28/29):** `SigmaLayer/ContextFixedA7.lean`,
  `SigmaLayer/ContextFixedA7FS.lean`.
- **★ STATUS / GUARD (2026-07-29): the base-only general-`N` route is PARKED.** Not because it is
  refuted — it is *not* — but because the decision-relevant output is already in hand and the
  remaining path is blocked. Do not resume it without a new idea that reaches the generic-`ψ`
  regime or supplies harmonic analysis on `ℂℙⁿ⁻¹`. **Successor question:** is the fibred
  `Σ = ℂℙⁿ⁻¹ × ℝ` a legitimate **A1 ontic sector**? Non-compact fibre, no Kähler structure, its
  measure not shown to be Liouville — and if contextuality lives in the fibre, that is now the
  load-bearing unproven thing. See the `BACKLOG.md` row.
