# Where measurement contextuality lives in Σ — the qubit / general-`N` boundary

> **A structural lesson about Σ, learned 2026-07-25…27.** Not a defect in CSD — a
> *constraint* on its structure. This doc states precisely what is proven, what is
> refuted, what is open, so it is not re-litigated. Read with
> [`record-layer-plan.md`](record-layer-plan.md) (MD-1) and
> [`CSD-CHARTER.md`](CSD-CHARTER.md).

## One-line lesson

**The Born rule is an ontic typicality volume for every `N` (a theorem). But *where the
measurement contextuality sits in Σ* is dimension-dependent: on the projective base for the
qubit, and necessarily in the fibre for `N ≥ 3`.** The elegant "regions on the Bloch sphere"
picture is a `CP¹ = S²` accident; it does not generalise as a base-only story.

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

3. **Base-only, context-fixed measurement — IMPOSSIBLE at `N ≥ 3`.** There is **no**
   `U(N)`-covariant, radial, nonnegative base density `g(|⟨ψ|φ⟩|²)` on `ℂℙⁿ⁻¹` with
   `∫_{Ωᵢ(M)} g dμ_FS = |⟨eᵢ|ψ⟩|²` for the max-overlap (Voronoi) cells and all `M, ψ`.
   - **Evidence:** (a) Phase-1 numerics on `ℂℙ²` — non-negative least-squares forces the
     covariant base density *negative* (`r_nn` plateaus ~10× the noise floor, stable under 4×
     samples; the qubit control passes). (b) Operator argument: the affine "dipole"
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

- **A7 as literally stated** ("epistemic outcome regions `{Ωᵢ(M)} ⊂ ℂℙⁿ⁻¹`") is the whole story
  **only at `N = 2`.** For `N ≥ 3` the operative regions are **fibre** regions over `Σ`, not on the
  projective base. This is a substantive revision, not cosmetic.
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
- **Guard:** [`record-layer-plan.md`](record-layer-plan.md) — do not re-propose base-only Voronoi
  context-fixing for `N ≥ 3`.
