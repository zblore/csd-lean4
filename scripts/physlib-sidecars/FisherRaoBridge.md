title: Fisher–Rao metric of the Born map

## overview

A unit vector `ψ : EuclideanSpace ℂ ι` has Born weights `‖ψ i‖ ^ 2`, a point of the open
probability simplex when no coordinate vanishes. A direction `u` at `ψ` displaces the weights by
`2 * Re (conj (ψ i) * u i)`, and the Fisher–Rao inner product of two displacements is
`∑ i, dp i * dp' i / p i`.

Along a torus-horizontal direction, one for which every `conj (ψ i) * u i` is real (the moduli
of the coordinates move and the phases do not), the sum collapses: the Fisher–Rao inner product
of the displacements along `u` and any `v` is `4 * Re ⟪u, v⟫`. For directions tangent to the
unit sphere at `ψ` this is the Fubini–Study inner product in the normalisation where the qubit
state space is the unit round sphere, so the Fubini–Study metric of a pure-state family is its
quantum Fisher information. The radial direction `u = ψ` is torus-horizontal but not tangent;
the projective form of the identity, on horizontal lifts, is in `BraunsteinCaves.lean`.

## key results

* `bornWeight`, `bornSimplex`: the Born weights of a vector, and as a point of `OpenSimplex ι`
* `bornDeriv`, `hasFDerivAt_bornWeight`: the displacement of the weights along `u` is the
  derivative of the Born map
* `sum_bornDeriv`: the displacement sums to `2 * Re ⟪ψ, u⟫`, so it is tangent to the simplex
  when `u` is tangent to the unit sphere
* `fisherRaoInner_bornDeriv`: for torus-horizontal `u` and any `v`,
  `fisherRaoInner (bornSimplex ψ) (bornDeriv ψ u) (bornDeriv ψ v) = 4 * Re ⟪u, v⟫`
* `fisherRaoSq_bornDeriv`: the Fisher–Rao quadratic form of a torus-horizontal displacement is
  `4 * ‖u‖ ^ 2`

## references

* S. L. Braunstein and C. M. Caves, Statistical distance and the geometry of quantum states,
  Phys. Rev. Lett. 72, 3439–3443 (1994). [ref: Braunstein:1994zz]
* I. Bengtsson and K. Życzkowski, Geometry of Quantum States, Cambridge University Press (2006;
  second edition 2017, sections 4.4 and 14.2). [ref: Bengtsson:2006rfv]

## docstring bornWeight

The Born weight of the `i`-th coordinate of `ψ`: `‖ψ i‖ ^ 2`.

## docstring bornWeight_def

`bornWeight`, unfolded.

## docstring bornWeight_nonneg

Born weights are nonnegative.

## docstring bornWeight_pos

The Born weight of a nonvanishing coordinate is positive.

## docstring bornDeriv

The displacement of the `i`-th Born weight along `u`: `2 * Re (conj (ψ i) * u i)`.

## docstring bornDeriv_def

`bornDeriv`, unfolded.

## docstring IsTorusHorizontal

A direction `u` at `ψ` is torus-horizontal when every `conj (ψ i) * u i` is real: it changes the
moduli of the coordinates and none of their phases. It need not be tangent to the unit sphere;
the radial direction `ψ` qualifies.

## docstring isTorusHorizontal_of_forall_eq

A direction whose coordinates are real multiples of those of `ψ` is torus-horizontal.

## docstring bornDeriv_mul_div_bornWeight

Pointwise form of the bridge: for `ψ i ≠ 0` and `conj (ψ i) * u i` real,
`bornDeriv ψ u i * bornDeriv ψ v i / bornWeight ψ i = 4 * Re ⟪u i, v i⟫`.

## docstring sum_bornWeight

The Born weights sum to `‖ψ‖ ^ 2`.

## docstring bornSimplex

The Born weights of a unit vector with no vanishing coordinate, as a point of the open simplex.

## docstring bornSimplex_val

The underlying weights of `bornSimplex`.

## docstring bornDerivCLM

`bornDeriv ψ · i` as a real continuous linear map: `2 * ⟪ψ i, · i⟫_ℝ`.

## docstring bornDerivCLM_apply

`bornDerivCLM` evaluates to `bornDeriv`.

## docstring hasFDerivAt_bornWeight

The Born map `ψ ↦ ‖ψ i‖ ^ 2` has derivative `bornDerivCLM ψ i` at `ψ`.

## docstring sum_bornDeriv

The displacement of the weights sums to `2 * Re ⟪ψ, u⟫`; it is tangent to the simplex when `u`
is tangent to the unit sphere at `ψ`.

## docstring fisherRaoInner_bornDeriv

The Fisher–Rao inner product of the Born displacements along a torus-horizontal `u` and any `v`
is `4 * Re ⟪u, v⟫`.

## docstring fisherRaoSq_bornDeriv

The Fisher–Rao quadratic form of a torus-horizontal Born displacement is `4 * ‖u‖ ^ 2`.
