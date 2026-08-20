# P4: the dispersion earned, not defined — scoping note

Created 2026-08-20, executed same day. Companion to
[`eft-pillars-plan.md`](eft-pillars-plan.md) (P4) and
[`necessity-audit.md`](necessity-audit.md) (which records the prior prose as
overstating: "dispersion is boost-covariant, but covariance is not shown to
select it"). See also `specs/future-work.md`.

## The gap, precisely

`CV/Dispersion.lean` **defines** `omega m p := √(p² + m²)` and `CV/Boost.lean`
proves the forward direction: the definition is boost-covariant on the nose
(`boost_omega`). Nowhere is the **converse** proved — that covariance *selects*
this dispersion. Without the converse, the relativistic content is written
down, not forced.

## What closes it (all landed in `CV/DispersionEarned.lean`)

Two independent selections, chained, with sharpness:

1. **The cone selects the boosts** (`cone_preserving_is_boost`): any linear map
   of the `(E, p)` plane that preserves the two light rays forward and has unit
   determinant IS a boost at some rapidity. The symmetry posit is only
   "linear + ray-preserving + unimodular"; the `cosh/sinh` form is derived
   (eigenvectors on the rays, reciprocal positive eigenvalues, so
   `χ = −arsinh b`).
2. **The boosts select the dispersion** (`boost_covariance_selects_omega`):
   if `ω 0 = m > 0` and the graph of `ω` is boost-covariant
   (`boostE χ (ω p) p = ω (boostP χ (ω p) p)` for all `χ, p` — exactly the law
   `boost_omega` proves for `omega m`), then `ω = omega m`. Proof: the single
   orbit through the rest point `(m, 0)` already covers every momentum
   (`χ = −arsinh(p/m)`), and single-valuedness pins `ω` on it. No continuity,
   no measurability, no evenness assumed.
3. **The characterisation** (★★ `cone_symmetry_characterises_omega`): for
   `m > 0`, `ω = omega m` **iff** `ω` has rest energy `m` and is covariant
   under every ray-preserving unimodular linear symmetry. Forward = (1)+(2);
   backward = `cone_preserving_is_boost` + the existing `boost_omega`
   (non-vacuity is the corpus's own theorem, not a toy).
4. **Sharpness of the mass gap** (`massless_covariance_not_selecting`): at
   `m = 0` the selection genuinely fails — `ω = id` (the right-moving ray) is
   boost-covariant with `ω 0 = 0` but is not `omega 0 = |p|`. So `0 < m` in
   (2)/(3) is necessary, not a convenience.

## Walls pre-checked (why this is bounded)

`Real.arsinh` with `sinh_arsinh` / `cosh_arsinh : cosh (arsinh x) = √(1 + x²)`
are in Mathlib (`Analysis/SpecialFunctions/Arsinh.lean`), plus
`cosh_add_sinh` / `cosh_sub_sinh` = `exp (±x)` for the positivity side goals.
Everything else is `ring`/`nlinarith` algebra over the existing
`CV/Boost.lean` API.

## Honest boundary

Kinematic level, inherited from `CV/Boost.lean`'s own scope: this is selection
of the **dispersion relation** by symmetry of the `(E, p)` plane. No boost
action on the finite mode lattice is claimed (a lattice is not
boost-invariant; standard cutoff honesty), and the identification of the
`(E, p)` light rays with the dynamical Lieb-Robinson cone is not claimed here —
the LR cone is an upper bound with a model-dependent velocity, not an exact
invariant set. What P4 asked for — "the difference between having written
relativity down and having it forced" — is closed at the level where the
corpus states relativity: the shell itself.
