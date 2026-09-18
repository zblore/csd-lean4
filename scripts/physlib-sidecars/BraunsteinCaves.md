title: Braunstein–Caves inequality for the coordinate readout

## overview

The classical Fisher information of the computational-basis readout of a pure-state family is
at most its quantum Fisher information, with equality exactly when the direction of motion
changes only the moduli of the coordinates. This file proves the inequality in two forms.

Algebraically, `fisherInfo (bornWeight ψ) (bornDeriv ψ u) ≤ 4 * ‖u‖ ^ 2` for every direction
`u`, with equality iff `u` is torus-horizontal. Here `4 * ‖u‖ ^ 2` is the quantum Fisher
information only for `u` tangent to the unit sphere.

Projectively, a point of the state space is a ray `[ψ]` with `ψ ≠ 0` and a direction at it is
any vector `u`; the pairs `(ψ, u)` and `(ψ, u + c • ψ)` describe the same tangent vector. The
unit vector on the ray is `normalize ψ`, the horizontal lift of `u` removes the component of `u`
along `ψ` and rescales, and the Fubini–Study inner product of two directions is
`fsInnerHom ψ u v`, which is `4 * Re ⟪horizontalLift ψ u, horizontalLift ψ v⟫`. The readout's
Fisher information along the lift of `u` is at most `fsInnerHom ψ u u`, which for unit `ψ` is
the quantum Fisher information `4 * (‖u‖ ^ 2 - ‖⟪ψ, u⟫‖ ^ 2)`, with equality iff the lift is
torus-horizontal.

## key results

* `fisherInfo_bornDeriv_le`, `fisherInfo_bornDeriv_eq_iff`: the algebraic bound and its
  equality case
* `normalize`, `horizontalLift`, `fsInnerHom`: homogeneous coordinates on the state space
* `inner_horizontalLift`: `fsInnerHom ψ u v = 4 * Re ⟪horizontalLift ψ u, horizontalLift ψ v⟫`
* `fisherRaoInner_bornDeriv_normalize`: the Fisher–Rao identity of `FisherRaoBridge.lean` in
  homogeneous coordinates
* `fsInnerHom_self_of_norm_eq_one`: for unit `ψ`,
  `fsInnerHom ψ u u = 4 * (‖u‖ ^ 2 - ‖⟪ψ, u⟫‖ ^ 2)`
* `fisherInfo_bornDeriv_horizontalLift_le`, `fisherInfo_bornDeriv_horizontalLift_eq_iff`:
  Braunstein–Caves for the coordinate readout, with its equality case

## references

* S. L. Braunstein and C. M. Caves, Statistical distance and the geometry of quantum states,
  Phys. Rev. Lett. 72, 3439–3443 (1994). [ref: Braunstein:1994zz]
* I. Bengtsson and K. Życzkowski, Geometry of Quantum States, Cambridge University Press (2006;
  second edition 2017, sections 4.4 and 14.2). [ref: Bengtsson:2006rfv]

## docstring bornDeriv_sq_div_bornWeight_le

Pointwise: `bornDeriv ψ u i ^ 2 / bornWeight ψ i ≤ 4 * ‖u i‖ ^ 2`, since `Re z ≤ ‖z‖`.

## docstring im_eq_zero_of_bornDeriv_sq_div_bornWeight_eq

Equality in `bornDeriv_sq_div_bornWeight_le` forces `conj (ψ i) * u i` to be real.

## docstring fisherInfo_bornDeriv_le

The Fisher information of the coordinate readout along `u` is at most `4 * ‖u‖ ^ 2`.

## docstring fisherInfo_bornDeriv_eq_iff

Equality in `fisherInfo_bornDeriv_le` holds exactly on the torus-horizontal directions.

## docstring normalize

The unit vector on the ray of `ψ`: `‖ψ‖⁻¹ • ψ`.

## docstring norm_normalize

`normalize ψ` has norm one for `ψ ≠ 0`.

## docstring normalize_apply

The coordinates of `normalize ψ`.

## docstring normalize_apply_ne_zero

`normalize ψ` has no vanishing coordinate where `ψ` has none.

## docstring bornWeight_normalize

The Born weights of the ray of `ψ`: `‖ψ k‖ ^ 2 / ‖ψ‖ ^ 2`.

## docstring horizontalLift

The horizontal lift of a direction `u` at `ψ`: the component of `u` orthogonal to `ψ`, scaled
by `‖ψ‖⁻¹`.

## docstring horizontalLift_apply

The coordinates of `horizontalLift ψ u`.

## docstring inner_normalize_horizontalLift

The horizontal lift is orthogonal to `ψ`, hence tangent to the unit sphere at `normalize ψ`.

## docstring fsInnerHom

The Fubini–Study inner product of two directions at `ψ`, in homogeneous coordinates:
`4 * (Re ⟪u, v⟫ / ‖ψ‖ ^ 2 - Re (⟪u, ψ⟫ * ⟪ψ, v⟫) / ‖ψ‖ ^ 4)`.

## docstring inner_horizontalLift_eq

The inner product of two horizontal lifts, as a complex number.

## docstring inner_horizontalLift

`fsInnerHom ψ u v = 4 * Re ⟪horizontalLift ψ u, horizontalLift ψ v⟫`.

## docstring conj_normalize_mul_horizontalLift

The coordinate product `conj (normalize ψ k) * horizontalLift ψ u k`, as a complex number.

## docstring bornDeriv_normalize_horizontalLift

The Born displacement of the ray along `u`, in homogeneous coordinates.

## docstring isTorusHorizontal_normalize_horizontalLift

If every `conj (ψ k) * u k` is real then the horizontal lift of `u` is torus-horizontal at
`normalize ψ`.

## docstring fisherRaoInner_bornDeriv_normalize

The Fisher–Rao inner product of the Born displacements of the ray along the horizontal lifts of
`u` (every `conj (ψ k) * u k` real) and `v` is `fsInnerHom ψ u v`.

## docstring fsInnerHom_self_of_norm_eq_one

For unit `ψ`, `fsInnerHom ψ u u = 4 * (‖u‖ ^ 2 - ‖⟪ψ, u⟫‖ ^ 2)`, the quantum Fisher information
of the family.

## docstring fsInnerHom_self_eq_norm_horizontalLift

`fsInnerHom ψ u u = 4 * ‖horizontalLift ψ u‖ ^ 2`.

## docstring fisherInfo_bornDeriv_horizontalLift_le

Braunstein–Caves for the coordinate readout: along the horizontal lift of `u`, the readout's
Fisher information is at most `fsInnerHom ψ u u`.

## docstring fisherInfo_bornDeriv_horizontalLift_eq_iff

Equality in `fisherInfo_bornDeriv_horizontalLift_le` holds exactly when the horizontal lift of
`u` is torus-horizontal.
