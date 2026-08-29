# csd-lean4

[![CI](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/zblore/csd-lean4/actions/workflows/ci.yml)

Constraint-Surface Dynamics posits one object: an ontic surface `Σ`, concretely
`ℂℙ^{N-1} × T²`, with a Liouville measure `μL` and a deterministic,
measure-preserving flow. A preparation is a region of `Σ`, an outcome a subregion
of it, and probability is read as a fraction of ontic volume. This repository is a
Lean 4 and Mathlib formalisation of the finite-dimensional quantum mechanics that
results.

Constraint-Surface Dynamics provides a machine-checked reconstruction of the
principal finite-dimensional measurement statistics and update structure on its
stated ontic witness: deterministic ontic dynamics give definite context-indexed
outcomes without stochastic collapse or branching; Born weights follow from the
Fubini-Study/Kähler moment-map geometry and are realised as the measures of
explicit ontic fibre outcome cells rather than postulated as an independent
probability law; and outcome conditioning reproduces the Lüders update.
Basis-selective decoherence is proved for a supplied measurement context.

## Results

| Result | Theorem | `#print axioms` |
|---|---|---|
| Born weight is a Fubini-Study volume ratio | `fs_born_volume_ratio_N_uncond` | propext, Classical.choice, Quot.sound |
| The flow on rays is `exp(-itH)` | `projectedFlow_schrodinger_form` | propext, Classical.choice, Quot.sound |
| Rank-one Lüders update is a pushforward | `swap_luders_born` | propext, Classical.choice, Quot.sound |
| Frequencies converge to Born weights | `pointer_born_frequency` | propext, Classical.choice, Quot.sound |
| Born basins carved by the de-isolation propagator | `shearDeIsolation_born` | propext, Classical.choice, Quot.sound |

## Axioms, of two kinds

Logical axioms: none beyond Lean's foundational triple (`propext`,
`Classical.choice`, `Quot.sound`), enforced per theorem by pinned `#guard_msgs`
checks on `#print axioms` in CI. Physical posits are separate and untouched by
that: the sector is posited, never derived; calibration of the exact-record
witnesses is a named posit; and the typicality reading enters as a hypothesis on
the types, which is why it never appears in `#print axioms`. See
[`AXIOMS.md`](AXIOMS.md) section 3.

## What is not claimed

- The sector is posited: the sector itself is posited, never derived.
- Instrument results are relative to a stated dilation.
- Each measurement witness pays one price under the proved trilemma.
- No symplectic manifold is built in Lean; "Kähler" names the geometric reading of the measures.

Full list: [`docs/TOUR.md`](docs/TOUR.md).

## Repository versus published papers

Where the repository and the published LF-series papers diverge, the repository is
current. Four results the papers record as imported named axioms are discharged at
HEAD: see [`specs/papers-vs-repo.md`](specs/papers-vs-repo.md).

## Verify it yourself

```bash
lake exe cache get       # Mathlib build cache
lake build               # the corpus (root target)
lake build CsdLeanTests  # the axiom audit: REQUIRED, root target does NOT run it
./scripts/check-claims.sh  # the epistemic-overclaim guard
```

## Where to go next

| If you want | Read |
|---|---|
| The precise claims and theorem names | [`docs/TOUR.md`](docs/TOUR.md) |
| A reading path through one sector | [`docs/PATHS.md`](docs/PATHS.md) |
| What is assumed versus proved | [`AXIOMS.md`](AXIOMS.md), [`specs/reconstruction-status.md`](specs/reconstruction-status.md), [`specs/connectivity-manifest.md`](specs/connectivity-manifest.md) |
| Every experiment, both branches | [`EMPIRICAL.md`](EMPIRICAL.md) |
| What is open, with effort grades | [`specs/BACKLOG.md`](specs/BACKLOG.md) |
| How the code is organised | [`CONVENTIONS.md`](CONVENTIONS.md), [`specs/INDEX.md`](specs/INDEX.md) |
| Release history | [`specs/archive/HISTORY.md`](specs/archive/HISTORY.md) |
| The papers | [`CITATION.cff`](CITATION.cff); [constraintsurfacedynamics.com](https://www.constraintsurfacedynamics.com) |
| Plain-language definitions | [glossary.constraintsurfacedynamics.com](https://glossary.constraintsurfacedynamics.com) |

## Layout

| Path | Contents |
|---|---|
| `CsdLean4/LF1/`-`LF6/` | The layered reconstruction |
| `CsdLean4/SigmaLayer/` | Records, measurement dynamics |
| `CsdLean4/CV/` | Continuous variables, field chain |
| `CsdLean4/Empirical/` | QM regression suite, CSD twins |
| `CsdLean4/Thermo/` | Thermodynamics |
| `CsdLean4/Mathlib/` | CSD-free general-purpose material |
| `CsdLean4/Tests/` | The axiom-pin ledger |
| `docs/`, `specs/` | Tour, paths, status, backlog |

## Citation

Repository: [`CITATION.cff`](CITATION.cff), carrying ORCID and repository URL.
Programme: the LF-series Zenodo record named there.
Background: [constraintsurfacedynamics.com](https://www.constraintsurfacedynamics.com).
Glossary: [glossary.constraintsurfacedynamics.com](https://glossary.constraintsurfacedynamics.com), the plain-language companion to the module headers.
