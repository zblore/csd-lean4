# Berry phase as holonomy — scoping note (BACKLOG #10, expert row G)

*Written 2026-09-21 before any Lean, as the row demands. The row's 2026-09-07 wall re-probe
stands and is repeated in §2 with the counts of the day. The outcome section at the end records
what was built the same day.*

## 1. What the theorem is

For a closed curve of unit vectors `ψ : [0, T] → S ⊂ ℋ` whose rays close, `ψ(T) = e^{iφ} ψ(0)`,
Aharonov–Anandan (1987) split the **total phase** `φ` into a **dynamical phase**
`δ = ∫₀ᵀ Im⟪ψ, ψ̇⟫ dt` (for a Schrödinger evolution `iψ̇ = Hψ` this is `−∫₀ᵀ ⟪ψ, Hψ⟫ dt`, minus
the time-integrated energy) and a **geometric phase** `β = φ − δ`, and proved that `β` depends
only on the closed curve of *rays* — it is invariant under `ψ ↦ e^{iθ(t)} ψ` for every
differentiable `θ`. Geometrically: `A = Im⟪ψ, dψ⟫` is the connection form of the canonical
`U(1)`-connection on the Hopf bundle `S^{2n+1} → ℂℙⁿ`, a curve with `A = 0` along it is a
**horizontal (parallel) lift**, and `β` is the phase the horizontal lift picks up around the loop:
`β` **is the holonomy**. Berry's 1984 phase is the adiabatic special case (a slowly driven
`H(R(t))` whose eigenstate follows the parameter loop), and by Stokes `β = −∫∫ ω_FS` over a
surface bounded by the loop in `ℂℙⁿ` — for a spin-½ around a cone, minus half the solid angle.
Aharonov–Bohm (1959) is, in Berry's reading, the same holonomy with the flux as the curvature.

## 2. What Mathlib has at the pin (db584cd6d), re-probed 2026-09-21

* covariant derivatives on vector bundles: `Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic,Metric,Torsion}.lean` — present;
* parallel transport: **1 file mentions the phrase** (`CovariantDerivative/Metric.lean`, in prose), **0 declarations**;
* holonomy: **0**; principal bundles: **0**; the Hopf bundle as a bundle: **0**.

So the bundle-theoretic statement ("the holonomy of the canonical connection on the tautological
bundle") cannot be *stated* at the pin. What can be stated is everything that lives on the sphere
and on `ℂℙⁿ` directly: the connection form as a function along a curve, horizontal lifts as curves,
and the phase they return with. That is the whole content of Aharonov–Anandan's theorem, and it
needs only the inner-product calculus Mathlib has (`HasDerivAt.inner`, the interval FTC).

## 3. What the corpus has

`ℂℙⁿ` with the Fubini–Study form (`fsForm`, symplectic and Kähler), the Schrödinger flow on it as
the Hamiltonian flow of `−2⟨H⟩` (`ProjectiveSpaceSchrodingerFlow.lean`), the unit-sphere lift
`exp(−itH) ψ₀` with its derivative (`schrodingerUnitary_hasDerivAt`), and the sector
`Σ = ℂℙⁿ × T²` whose fibre is a torus of *record* phases, not a `U(1)`-bundle over configuration
space. The second obstruction of the row is therefore permanent and is not a Mathlib gap: a
Berry phase lives on the Hopf bundle over the *base* `ℂℙⁿ`; the `T²` fibre of `Σ` carries the
record layer's phases and is a different object. The honest CSD reading is stated in §5.

## 4. The bricks

| Brick | Statement | Price | Built? |
|---|---|---|---|
| **BP-1** | **Aharonov–Anandan geometric phase, on the sphere.** `connectionForm ψ t = Im⟪ψ t, ψ̇ t⟫`, `dynamicalPhase = ∫₀ᵀ A`, `geometricPhase = φ − dynamicalPhase`; ★★ gauge invariance `geometricPhase (e^{iθ} ψ) = geometricPhase ψ` for every differentiable `θ`; ★ the horizontal lift `e^{−i∫A} ψ` has `A = 0` and returns with exactly `e^{iβ}` — **the geometric phase is the holonomy**; ★ for a Schrödinger evolution with self-adjoint `H`, `A = −⟪ψ, Hψ⟫` and the energy is conserved, so `β = φ + T ⟨H⟩`. Category 1. | **M** | **yes, 2026-09-21** |
| **BP-2** | **The spin-½ cone (Berry's example).** `ψ(t) = (cos θ/2, e^{it} sin θ/2)` over `[0, 2π]`: `A = sin²(θ/2)`, `φ = 0`, `β = −2π sin²(θ/2) = −π(1 − cos θ)` = **minus half the solid angle** of the cone. Category 3. | **S–M** | **yes, 2026-09-21** |
| **BP-3** | **The curvature formula** `β = −∫∫ ω_FS` (Stokes on `ℂℙⁿ` for a loop bounding a disc): needs surface integrals of a 2-form pulled back along a `C¹` map of the disc — the pin has neither Stokes nor surface integrals of forms. Honest shape: for loops in a chart, the pullback to the plane and Green's theorem (also absent at the pin). | **M–L** | **yes, 2026-09-23** (`GeometricPhaseCurvature.lean`, `BerryPhaseCurvature.lean`: the disc in polar form on a rectangle, Mathlib's divergence theorem as Green, curvature `2 Im⟪∂_sΨ, ∂_tΨ⟫`; the `fsForm` identification is BACKLOG #65) |
| **BP-4** | **Aharonov–Bohm, discrete.** The finite-dimensional AB effect: a ring of `N` sites with Peierls phases `e^{iΦ/N}` on the hops; the spectrum `2 cos((2πk + Φ)/N)` depends on the flux `Φ` only mod `2π` and is invariant under the gauge transformation that moves all the phase onto one bond — the flux is observable, the vector potential is not. Category 1 (a circulant matrix and its eigenvectors) with a QM-side reading. The `L²(S¹)` version (`−(∂ − iΦ)²`, spectrum `(n − Φ)²`) is CV-scale and not proposed. | **S–M** | no — BACKLOG #55 |
| **BP-5** | **Berry's adiabatic theorem**: the eigenstate of a slowly driven `H(R(t))` follows the parameter loop up to `e^{i(φ_dyn + β)}` with error `O(1/T)`. The adiabatic theorem is a genuine asymptotic ODE result (Kato 1950) absent from Mathlib and from the corpus. | **XL** | no — BACKLOG #56, not recommended |

## 5. The CSD reading, and what the "twin" honestly is

BP-1's gauge invariance is the CSD statement: **the geometric phase is a function of the projected
closed orbit in the sector** `ℂℙⁿ`, unchanged by any differentiable rephasing of the lift — in
particular by the record-layer's torus phases, which enter the lift exactly as such rephasings.
Nothing in `Σ`'s fibre carries a holonomy of its own, and the note claims none: the fibre is not a
`U(1)`-bundle over configuration space (the row's second obstruction), and the "phase holonomy on
the fibre" that ER3 hoped for is not a well-posed object. The twin of ER3 is therefore BP-1 read on
the sector's Schrödinger orbits plus BP-4 for the flux experiment; ER3's status line in
`qm-empirical-tests.md` says so.

## 6. Outcome (2026-09-21)

BP-1 landed as `Mathlib/Analysis/InnerProductSpace/GeometricPhase.lean` (Category 1) and BP-2 as
`Empirical/QM/BerryPhase.lean` (Category 3); see the module headers and `BACKLOG.md` #10 for the
theorem list and pin counts. BP-3 landed 2026-09-23 (`BACKLOG.md` #54; its `fsForm` identification is #65); BP-4, BP-5 are #55–#56. The row's "L" was the
price of the bundle-theoretic statement, which is not stateable at the pin; the stateable half
took M.

## References

Y. Aharonov, J. Anandan, *Phase change during a cyclic quantum evolution*, PRL 58 (1987) 1593;
M. V. Berry, *Quantal phase factors accompanying adiabatic changes*, Proc. R. Soc. A 392 (1984) 45;
B. Simon, *Holonomy, the quantum adiabatic theorem, and Berry's phase*, PRL 51 (1983) 2167;
Y. Aharonov, D. Bohm, *Significance of electromagnetic potentials in the quantum theory*, Phys.
Rev. 115 (1959) 485; A. Tomita, R. Chiao, PRL 57 (1986) 937 (the measured Berry phase);
A. Tonomura et al., PRL 56 (1986) 792 (the measured AB phase).
