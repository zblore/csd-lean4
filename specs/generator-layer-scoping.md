# The generator layer (step 4) and `R-016`, re-priced after step (3): scoping note

**Status:** SCOPED 2026-09-08 (evening, after `c4e295d`). **G1 BUILT the same evening**
(`Mathlib/Geometry/Manifold/HamiltonianVectorField.lean`, 13 pins): `interiorProduct`,
`IsHamiltonianVectorField`, `IsLocallyHamiltonian`, and what alternation and linearity give for free —
★ `mfderiv_apply_self` (`dH (X) = 0`), ★ `unique_of_isSymplectic`, linearity in `H`. The **S** held; the one
non-mechanical point was that `TangentSpace` carries no normed instance at the pin, so `curryLeft` and every
linearity lemma had to be forced onto the model space `E` by explicit `(E := E)` and finished by `calc`, never
`rw` (the module-system instance-path trap again). **G6 BUILT the same night**
(`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceMomentMap.lean`, 15 pins): ★★★
`torusField_isHamiltonianVectorField` — the velocity field of the torus action `p ↦ diag(e^{iθ}) • p`
on `ℂℙⁿ` (★ proved to be that velocity, `hasDerivAt_chartFun_torusUnitary`) is the Hamiltonian
vector field of `2 ∑ₖ θₖ · momentMap` for `fsForm`. The **L** came in under: no pullback of forms was
needed (the §5 stop condition never triggered), the derivative of the action was one `HasDerivAt` of a
phase, and the content was the single chart identity `ω_w(X_w, v) = dH_w v` through M7's
`fsModelForm_apply` — the sums were the work, not the geometry. Two shelf facts worth recording: at the
pin `HasFDerivAt` has no quotient rule and no inverse-of-a-function rule (only `hasFDerivAt_inv` for
`x ↦ x⁻¹`), so `2N/D` is differentiated as `N · D⁻¹` by composition; and `Complex.exp` on `ℝ` is
differentiated through `Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt`. ⚠️ The factor `2` is the `-4`
convention of `fsChartForm`. **The `TERMS.md` moment-map line is discharged.** **G8 BUILT 2026-09-08 (late; 9 pins)** exactly
as §8 planned: ★★ `eq_add_const_of_isHamiltonianVectorField` (uniqueness up to a constant on `ℂℙⁿ`,
no connectedness lemma — `is_const_of_fderiv_eq_zero` on each whole chart image plus the point
`[1 : ⋯ : 1]`) and ★★★ `eq_torusHamiltonian_of_nonneg_of_sum` (the normalisation pins it to
`2 · momentMap`). The **M** held; the stop condition never triggered — the chart bridge was
`mfderiv_comp` with the chart inverse (`mdifferentiableAt_atlas_symm`) and `mfderiv_eq_fderiv`, not
`MDifferentiableAt.mfderiv`. `POSITS.md` bullet 1's "unformalised" is now formalised; **Posit 1 is
unchanged.** **G9 + G10 BUILT 2026-09-09 (11 pins)** as §8 priced, in the same module: ★★
`range_momentMap` — the image of `momentMap` is exactly `stdSimplex ℝ (Fin (n + 1))`, `⊆` the
normalisation and `⊇` the ray of `(√t₀, …, √tₙ)` (`sqrtVec`, `momentMap_mk_sqrtVec`); the polytope of
this action by computation, the Atiyah–Guillemin–Sternberg theorem untouched. ★
`fsVolume_map_torusUnitary_smul` / `measurePreserving_torusUnitary_smul` — every map of the torus
flow preserves `fsVolume n`, with `torusUnitary_add_smul` the one-parameter group law; a corollary
of `fsVolume_map_smul`, Liouville in the dynamics sense for this one flow, G5 still unscheduled and
**Posit 3 untouched**. The **S–M** and **S** held; nothing non-mechanical. **G11 BUILT 2026-09-09 (7
pins)**: the `0`-form API `ExteriorDerivative.lean`'s header listed as absent — `zeroFormFamily f`,
`localRep_zeroFormFamily`, `contMDiff_zeroFormFamily` (the section is `C^∞`, by `contMDiffAt_section`
and `constOfIsEmptyLIE ∘ f`), the bundled `zeroForm`, ★ `toFlat_mextDeriv_zeroFormFamily` (**`d` of a
`0`-form is its differential**, from `extDeriv_constOfIsEmpty` and the `MDifferentiableAt.mfderiv`
chart bridge) — and ★ `IsHamiltonianVectorField.isLocallyHamiltonian` (`HamiltonianVectorField.lean`):
`ι_X ω = dH` as families, so `d(ι_X ω) = d(dH) = 0` by `mextDeriv_mextDeriv`, for a `C^∞` energy.
The **M** came in under: the one non-mechanical point was the module-system instance path
(`Trivial M ℝ x` vs `TangentSpace 𝓘(ℝ, ℝ) (H x)`), finished pointwise through `toFlat` and `trans`,
never by `rw`. The converse (locally Hamiltonian ⇒ Hamiltonian) is false and not stated. **G13 BUILT
2026-09-09 (new module `Instances/ProjectiveSpaceSchrodingerFlow.lean`, 25 pins)**: ★★★
`schrodingerField_isHamiltonianVectorField` — for every Hermitian `H` the flow `p ↦ exp(-itH) • p`
(the corpus's projected Schrödinger flow, `CSD.LF4.schrodingerUnitary`, ★ proved to be the velocity
through `schrodingerUnitary_hasDerivAt` and a matrix-entry functional under the `L2Operator` norm)
is Hamiltonian for `fsForm` with Hamiltonian `-2 ⟨H⟩ = -2 ⟪z, Hz⟫.re/‖z‖²` (`expectation`,
`schrodingerHamiltonian`); G6's torus is the diagonal case (`schrodingerHamiltonian_neg_diagonal`).
The **M–L** came in as **M**, and by a different route than G6's: the chart identity ★★
`fsModelForm_schrodingerChartField` is proved in the AMBIENT inner product — the tangent lift
`insertZeroCLM` preserves the inner products `fsModelForm_apply` is written in, the lifted velocity
is `-i (Hv - (Hv)_i v)`, the `(Hv)_i` terms cancel, and what remains is `Im (i z) = Re z` plus the
symmetry of `H` (`isSymmetric_toEuclideanLin_iff`); the chart Hamiltonian is differentiated by
`HasFDerivAt.inner` along the affine lift, no coordinate sums anywhere. Shelf facts: this Mathlib's
`RCLike.inner_apply` puts the conjugate on the RIGHT; `inner_self_eq_norm_sq_to_K` casts through
`RCLike.ofReal`, not `Complex.ofReal`, so work with `re`/`im` of the atoms instead. Posit 1 untouched.
**G2 BUILT 2026-09-09 (14 pins, `HamiltonianVectorField.lean` + two corollaries in
`ProjectiveSpaceSchrodingerFlow.lean`)** exactly as §2 priced: `flatAt α x : E →ₗ[ℝ] Module.Dual ℝ E`
is `v ↦ α x (v, ·)` (`LinearMap.mk₂` on the four slot-linearity lemmas), non-degeneracy at `x` is its
injectivity, `Subspace.dual_finrank_eq` makes it a `LinearEquiv`, and ★★ `hamiltonianVectorField α hnd
H = fun x => (ω♭ₓ)⁻¹ (dH_x)` with **existence** (`hamiltonianVectorField_isHamiltonianVectorField`)
and **uniqueness** (`IsHamiltonianVectorField.eq_hamiltonianVectorField`); `IsSymplectic.
hamiltonianVectorField` specialises. On `ℂℙⁿ` the torus field and the Schrödinger field ARE the
constructed fields (`torusField_eq_hamiltonianVectorField`, `schrodingerField_eq_hamiltonianVectorField`).
The **M** held; the only friction was the instance path `E` vs `TangentSpace 𝓘 x` — every `rw` of a
`flatAt_apply`-shaped lemma across it fails, `exact`/`trans` by defeq succeeds — and the fact that
inside a `theorem IsSymplectic.foo` declaration a bare name resolves into `IsSymplectic.` first (write
`DifferentialForm.foo`). Pointwise only; the smooth section is G3. Shelf fact: nobody imported
`Instances/ProjectiveSpaceFubiniStudySymplectic.lean` before this — it was a root-only leaf.
**G3 BUILT 2026-09-09 (16 pins, `HamiltonianVectorField.lean` + five corollaries in
`ProjectiveSpaceSchrodingerFlow.lean`)** by the route §2 priced — the `VectorBundle/Hom.lean` pattern:
★★★ `contMDiff_hamiltonianVectorField`, **G2's field `x ↦ (ω♭ₓ)⁻¹ (dH_x)` is a `C^∞` section of the
tangent bundle** for a `C^∞` non-degenerate 2-form and a `C^∞` energy. In the tangent trivialisation
at `x₀` the field is `localHamiltonianVector` — `ContinuousLinearMap.inverse (curryLeft (localRep α x₀
w))` applied to the chart derivative of `H` — by *uniqueness at the flat level* (★★
`trivializationAt_hamiltonianVectorField_snd`: `trivializationAt_snd` intertwines `α` with its local
representative, `mfderiv_comp` intertwines `dH` with the chart derivative; `localRep_nondegenerate`
carries non-degeneracy across through `symmL`/`continuousLinearMapAt`); and ★★
`contDiffAt_localHamiltonianVector` is `contDiffAt_map_inverse` at the invertible point (`flatCLE`,
G2's `flatEquiv` made continuous by `LinearEquiv.toContinuousLinearEquiv`), with `curryLeft` a bounded
linear map, `contDiffAt_localRep`, and `fderiv_right`. Corollaries: both Hamiltonians on `ℂℙⁿ` are
`C^∞` (`contMDiff_schrodingerHamiltonian`, inner-product calculus in the chart + `contMDiffAt_iff`;
`contMDiff_torusHamiltonian` by the diagonal identity), so ★★ **the torus field (G6) and the
Schrödinger field (G13) are `C^∞` vector fields** (`contMDiff_torusField`, `contMDiff_schrodingerField`).
The **M–L** came in as **L**: `contDiffAt_ring_inverse` was never needed (`contDiffAt_map_inverse` on
`E ≃L (E [⋀^Fin 1]→L ℝ)` is the tool), but the plumbing had three walls worth recording. (1) The
alternating-map space `E [⋀^Fin 2]→L ℝ` has no `FiniteDimensional` instance, and any `→L` type
*declared* with it as domain picks the raw topological-module instances, which do not unify with
Mathlib's normed-space lemmas — so the flat map is stated through `curryLeft` (Mathlib's
`curryLeftLI`/`norm_curryLeft`) and its smoothness through `IsBoundedLinearMap.contDiff` with the
witness elaborated *against the lemma's expected type*, never as a CLM on that space. (2) A constant
family `fun _ : E => ξ` is only defeq-typed as a bundle family; every `rw` on a goal containing it
fails with "not type-correct under implicit transparency" — wrap it in a def (`flatFamily`) so it
is syntactically fibre-typed. (3) `ω` is scoped notation under `open scoped ContDiff` and cannot
be a binder name; a leading `.foo` on a new line is a dot-ident against the expected type, not
dot notation. **G4 BUILT 2026-09-09 (13 pins, `HamiltonianVectorField.lean` + six corollaries in
`ProjectiveSpaceSchrodingerFlow.lean`)** as §2 priced — direct applications: ★★
`exists_isMIntegralCurveAt_hamiltonianVectorField` (`exists_isMIntegralCurveAt_of_contMDiffAt` on G3's
`C^1` section, boundaryless model), ★★ `isMIntegralCurve_hamiltonianVectorField_eq`
(`isMIntegralCurve_eq_of_contMDiff`, Hausdorff), and ★★ `IsHamiltonianVectorField.comp_eq_of_isMIntegralCurve`
— **energy conservation** — from G1's `dH (X) = 0` and `is_const_of_deriv_eq_zero`; the `IsSymplectic.`
forms specialise. On `ℂℙⁿ`: the same three for `schrodingerField`, ★★
`expectation_eq_of_isMIntegralCurve_schrodingerField` (`⟨H⟩` conserved along every integral curve),
and ★★★ `isMIntegralCurve_schrodingerUnitary_smul` — **the Schrödinger flow `t ↦ exp(-itH) • p` IS the
integral curve of its field**, for every `p` (chart curve `s ↦ chartFun (exp(-i(s-t)H) • q)` by the group
law, derivative at `s = t` from G13's velocity lemma through the scalar chain rule), hence ★★
`expectation_schrodingerUnitary_smul`: `⟨H⟩` is conserved by the flow. The **S–M** held. Two shelf facts:
`HasFDerivAt.hasDerivAt` gets stuck on `TangentSpace 𝓘(ℝ, ℝ) _` in the codomain — unfold `HasDerivAt`
to its `smulRight` form and use `congr_fderiv` + `ContinuousLinearMap.ext_ring` instead; and a
`HasDerivAt` at a shifted point wants a named `have` at `t - t`, not an inline `by rw [sub_self]`, before
`HasDerivAt.scomp (h := fun s => s - t) (x := t)`. Not stated: a global flow of a general Hamiltonian
field (Mathlib has no flows on manifolds — G5's wall), and the torus orbits (same route, not written).
**G7 BUILT 2026-09-09 (13 pins)**: `DifferentialForm.IsAlmostKahler β J` (`HamiltonianVectorField.lean`)
— a symplectic form with a compatible almost complex structure, `J² = -1`, `J`-invariance, taming
`β (J v, v) > 0` — with its metric `g = β (J ·, ·)` symmetric (★ `metric_comm`, from `J`-invariance,
`J² = -1` and the new antisymmetry lemma `apply_swap`) and positive definite; on `ℂℙⁿ` ★★
`fsForm_isAlmostKahler` (`Instances/ProjectiveSpaceFubiniStudySymplectic.lean`): **`ℂℙⁿ` with the
Fubini–Study form and `J = i·` is almost Kähler** — `fsForm_smul_I_smul_I` (a `(1,1)`-form, by
`fsModelForm_apply`) and the taming `fsSection_smul_I_neg`, its `-4` sign absorbed by the convention
`g = ω (J ·, ·)` (so the spec's `g = ω(·, J·)` became `ω = g(·, J·)`, `apply_eq_metric`); and ★
`fderiv_chart_transition_smul_I` / `fsJ_symmL` — **`J` is the complex structure of the atlas**: the
transitions are `uTrans 1` (`chart_transition_eq_uTrans`), holomorphic by `contDiffOn_uTrans`, so
their derivatives are `ℂ`-linear and `J = i·` reads as `i·` in every chart. Named *almost* Kähler
on purpose: integrability of `J` as a vanishing Nijenhuis tensor is not stated, nor is `J` a smooth
section of the endomorphism bundle. The **M** held. One shelf fact: a type ascription on a
definitionally equal term is *erased* — `(v : Fin n → ℂ)` for `v : TangentSpace 𝓘 x` leaves `v`
tangent-typed, so `Complex.I • v` finds no `ℂ`-action; the reducible cast `tangentToModel` (the
`toFlat` idiom) is what actually changes the elaborated type.
**The step-(4) ladder is complete: G5 was built 2026-09-11/12 as Q29 (a)–(d′) on the chart route (§11); G12, G14a, G14b, G15, G16 and G19 were built 2026-09-10; G17 on 2026-09-11.**
Every rating for step (4)
and for `R-016` in [`BACKLOG.md`](BACKLOG.md) was written before `mextDeriv`, `IsSymplectic`,
`topFormMeasure` and the top-power identity existed; this note re-prices them against what is in the
tree now. Every shelf claim below was grep-probed at the pin on 2026-09-08, per
[`exterior-derivative-scoping.md`](exterior-derivative-scoping.md) §3a: price by what is *missing*,
and confirm each "missing" by grep.

Items carry reference numbers (`G1`–`G7`, `R-016′`) so they can be named without ambiguity.

---

## 1. What exists now

**Corpus, manifold level (steps 0–3, all landed 2026-09-07/08):** `ℂℙⁿ` as an analytic manifold
(`Instances/ProjectiveSpace.lean`); `DifferentialForm` and the exterior derivative `mextDeriv` with
`d ∘ d = 0` (`Geometry/Manifold/ExteriorDerivative.lean`); the Fubini–Study form as a global `C^∞`
2-form with `fsForm_mextDeriv : d ω_FS = 0`; `DifferentialForm.IsSymplectic` and ★★★
`fsForm_isSymplectic`; the measure of a top form (`topFormMeasure`) and ★★★
`fsVolume_eq_smul_fubiniStudyMeasure : ω_FS^{∧n} = (4π)ⁿ · μ_FS`; the `U(n+1)` action in charts
(`uTrans`, `fsModelForm_uTrans`) and its linear rotation form (`fsModelForm_mulVec`).

**Corpus, below manifold level — what step (4) has to lift:** the linear Hamiltonian duality
`fundamentalForm_hamiltonianVectorFieldOf : ω (X w) v = g w v` (`HamiltonianVectorField.lean`); the
linear moment-map equation `IsPhaseHamiltonian` with `generatedRateField_eq_momentMap` (CR-15,
`RecordLayer/CellLawForced.lean`); the Darboux-chart Poisson bracket and conservation
(`SigmaLayer/ChartBracket.lean`); chart-level integral curves `IsHamiltonianCurve`,
`translationCurve_isHamiltonianCurve`, `translationCurve_unique`
(`SigmaLayer/ChartIntegralCurve.lean`); the stroke generation `strokeCurve_hasDerivAt_hamiltonianField`
(`RecordLayer/HamiltonianShift.lean`); and the **flux correction** of `RecordLayer/PiecewiseHamiltonian.lean`:
on `T²` the translation field has `ι_X ω = a·dp`, closed and not exact, so the measurement pieces are
*locally* Hamiltonian and have no global generating function.

**Mathlib at the pin, present:** vector fields as `Π x, TangentSpace I x`, with `VectorField.mlieBracket`
and `mpullback` (`Geometry/Manifold/VectorField/{LieBracket,Pullback}.lean`); **integral curves on
manifolds with existence and uniqueness** (`Geometry/Manifold/IntegralCurve/{Basic,ExistUnique,UniformTime,Transform}.lean`:
`exists_isMIntegralCurveAt_of_contMDiffAt`, `isMIntegralCurve_eq_of_contMDiff`, boundaryless variants);
the continuous interior product `ContinuousAlternatingMap.curryLeft`
(`Analysis/Normed/Module/Alternating/Curry.lean`); product charted spaces (`prodChartedSpace`); `Circle`
as an analytic manifold (`Instances/Sphere.lean`).

**Mathlib at the pin, absent (0 declarations):** Hamiltonian vector field, moment map, Poisson bracket,
symplectic form (the only hits for the words are `LinearAlgebra/SymplecticGroup.lean` and
`Analysis/Hofer.lean`, neither a manifold object); **global flows** of a vector field on a manifold
(integral curves only — no flow map, no smooth dependence on the initial point); Lie derivative and
Cartan's formula; Liouville's theorem; **`AddCircle` as a manifold** (`Geometry/Manifold/` has no
`AddCircle` at all — only the multiplicative `Circle` in `ℂ`); and, on our own side, the pullback of
differential forms along a smooth map (the deviation `top-power-scoping.md` recorded: invariance was
consumed in chart form and the general pullback was never built).

## 2. Step (4), as seven sub-bricks

| # | Brick | Cx | P(success) | Value | Depends on | What it lands, honestly |
|---|---|---|---|---|---|---|
| **G1** | `IsHamiltonianVectorField ω X H`: for a 2-form `ω`, a vector field `X : Π x, TangentSpace 𝓘 x` and `H : M → ℝ`, the equation `∀ x v, ω x ![X x, v] = mfderiv 𝓘 𝓘(ℝ, ℝ) H x v`; with `IsLocallyHamiltonian ω X := mextDeriv (ι_X ω) = 0` beside it | **S** | High | Medium | — | The word "Hamiltonian" at manifold level, which `TERMS.md` lacks. A predicate, nothing derived; the ℂℙⁿ inhabitants come from G6. `ι_X ω` is `curryLeft` pointwise; it is a 1-form as a *family*, and its smoothness is G3's problem, not G1's |
| **G2** ✅ built 2026-09-09 | Existence and uniqueness of `X_H` pointwise: on a finite-dimensional tangent space `ω♭ x : v ↦ ω x (v, ·)` is injective by non-degeneracy, hence bijective, so `X_H x := (ω♭ x)⁻¹ (dH x)` | **M** | High | Medium | G1 | `TangentSpace 𝓘 x = E` by `rfl`; `LinearMap.injective_iff_surjective` on `E` and its dual. Pointwise only |
| **G3** ✅ built 2026-09-09 | `X_H` is a smooth section of the tangent bundle | **M–L** | Medium–high | Medium (gates G4) | G2 | Inversion of `ω♭` along the bundle: `contDiffAt_ring_inverse` on the units plus the `localRep` chart plumbing that `ExteriorDerivative.lean` already does for forms. This is the `VectorBundle/Hom.lean` pattern again |
| **G4** ✅ built 2026-09-09 | Integral curves of `X_H` exist and are unique, and `H` is conserved along them (`ι_X ω (X) = 0` by alternation) | **S–M** | High | Medium | G3 | Direct application of Mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt` and `isMIntegralCurve_eq_of_contMDiff`; lifts `conserved_along_translationCurve` from the chart to the manifold |
| **G5** ✅ built 2026-09-11/12 as Q29 (a)–(d′) | Liouville at manifold level: the time-`t` map of `X_H` preserves `topFormMeasure (ω^{∧n})` — `IsSymplectic.map_hamiltonianFlow_topFormMeasure_wedgePow`, `fsVolume_map_hamiltonianFlow` (§11) | **XL** (took L–XL on the chart route) | Low | Medium, and less than it looks | G3, and two absent Mathlib layers | ⛔ *(original assessment)* Needs global flows (absent) and `L_X ω = 0` by Cartan's formula (absent). It would replace the posit `ConstraintDynamics.flow_preserves` by a theorem — **for Hamiltonian flows only**, and the corpus's measurement pieces are *not* globally Hamiltonian (the flux correction), so it would not touch the dynamics the record layer actually uses. **Queued** — §9, re-priced there (the author's decision, 2026-09-10) |
| **G6** | The moment map of the torus action on ℂℙⁿ at manifold level: the fundamental vector field `X_A` of `p ↦ exp(tA)·p` (the `t`-derivative of `uTrans`, which `contDiffOn_uTrans` already makes smooth), `μ_A [z] = ⟨z, iA z⟩/‖z‖²`, and ★★★ `IsHamiltonianVectorField fsForm X_A μ_A`; for `A = diag(iθ)` this is `LF4.momentMap` | **L** | Medium | **High** | G1 only (the field is given, G2/G3 are not needed) | Closes the `TERMS.md` moment-map line "NOT established: that it is the moment map of a Hamiltonian torus action on the symplectic *manifold*". It is also exactly the route the 2026-08-02 review recorded for the Hamiltonian-origin row: unitary rotations on a compact Kähler pointer are globally Hamiltonian (`H¹(ℂℙ^K) = 0`). The computation is `fsModelForm_apply` (M7) against the derivative of the action in the chart; half of it exists |
| **G7** ✅ built 2026-09-09 (as `IsAlmostKahler`) | A manifold-level Kähler predicate `IsKahler ω J g` on ℂℙⁿ: `J = i·` on each tangent space (chart-independent because the transitions are ℂ-analytic, `contDiffOn_uTrans`), `g = ω(·, J·)`, the pointwise triple `IsFubiniStudyKahler` lifted | **M** | High | Low–medium | — | Packages words the corpus already has pointwise; closes the last non-analyticity item of the `TERMS.md` Kähler line. Gates nothing |

**Recommended order: G1 → G6.** Together **L**, P(success) medium, value high — the one brick on
this ladder that discharges a line of `TERMS.md` rather than adding a word to it. G2–G4 are Mathlib
staging of independent worth (S–M each after G3) and can follow if wanted; G7 is cosmetic; G5 is not
scheduled.

## 3. `R-016`, re-priced (`R-016′`)

`R-016` asks for the arena-level statement that the back-reacting measurement map `jointLift` is the
time-1 map of a Hamiltonian flow on the arena manifold `ℂℙⁿ × T² × …`. Its 2026-09-02 pricing said
"Mathlib has no symplectic form, no Poisson bracket, no exterior derivative". **That wall is gone.**
What remains, in order:

1. **The arena as a manifold.** `KSigma N = CPN N × KTorus` with `KTorus = AddCircle 1 × AddCircle 1`.
   Products are fine (`prodChartedSpace`), but **`AddCircle` has no `ChartedSpace` at the pin**; only
   `Circle` does. Transporting one along `AddCircle.toCircle` is **S–M**; changing the corpus torus type
   is ⛔ (pin stability). Cx **S–M**.
2. **The arena 2-form.** `pr₁* ω_FS + pr₂* (dq ∧ dp)` needs the pullback of forms along the
   projections — the unbuilt piece — or a direct product-chart construction of the form. Cx **M–L**.
3. **The statement itself.** By the flux correction it is **false as a global statement**: the
   translation pieces satisfy `d(ι_X ω) = 0` and *not* `ι_X ω = dH`. The strongest honest
   manifold-level sentence is `IsLocallyHamiltonian` (G1's second predicate) for the shear field on
   the arena, together with the non-exactness — which is the classification
   `PiecewiseHamiltonian.lean` already proves in the chart. Cx **S** given G1 and (1)–(2).

**`R-016′` = (1) + (2) + G1: Cx L, P(success) medium, value medium.** ⚠️ It formalises the
residue's *statement* in the manifold vocabulary and records the obstruction as a theorem there; it
does **not** discharge `R-016`, whose content is the identification `jointLift = time-1 map`, a
paper-side end state (`residues.tsv`, `frozen-base-obstruction-scoping.md`). The residue row stays
open and its wording stays. The only route the review ever recorded for a *global* Hamiltonian
reading is the compact Kähler pointer, and that route is G6.

## 4. Traps

* **`AddCircle` vs `Circle`.** Do not let a manifold instance change a corpus type; the pins on
  `KTorus` are the record-layer spine. Transport, or restate on `Circle` in prose.
* **`mfderiv` of a real function is a covector, not a `Fin 1`-form.** G1 states `dH` as
  `mfderiv 𝓘 𝓘(ℝ, ℝ) H x : TangentSpace 𝓘 x →L[ℝ] ℝ`; do not build a `DifferentialForm` for it —
  `ContinuousAlternatingMap.ofSubsingleton` moves between the two if ever needed.
* **The fundamental vector field is a derivative in `t`, not in the chart variable.** For G6 use
  `HasDerivAt` of `t ↦ uTrans (exp (t A)) i i w` at `t = 0`, which is the derivative of a
  matrix exponential composed with an analytic map; `hasDerivAt_exp_smul_const` exists at the pin
  (`Mathlib/Analysis/SpecialFunctions/Exponential.lean`, grep-confirmed 2026-09-08).
* **No general pullback of forms.** G6 and `R-016′` (2) are where its absence bites; if either needs
  more than a chart computation, build the pullback first as its own S–M brick rather than working
  around it twice.
* **`momentMap` is guarded.** Any declaration whose name contains `momentMap`, `Hamiltonian`,
  `symplectic` or `Liouville` must be registered in `check-claims.sh`'s inventory with a parity
  justification before it will build past CI.

## 5. Deliverables and stop condition

**Deliverables** (each with pins in `Tests/AxiomAudit/MathlibStaging.lean`, each root-imported):
`Mathlib/Geometry/Manifold/HamiltonianVectorField.lean` (G1–G2);
`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceMomentMap.lean` (G6). Both are registered in
`scripts/check-doc-promises.sh` as promised-not-yet-built; remove each entry when its brick lands.

**⛔ Stop condition.** If the fundamental vector field of the torus action needs the differential of a
manifold map beyond what `contDiffOn_uTrans` and `mfderiv` in charts give — if it needs the general
pullback — stop, build the pullback as its own brick, and re-scope. If G1's statement does not
typecheck against `DifferentialForm 𝓘 M ∞ (Fin 2) ℝ` without an `ofSubsingleton` detour, the shape
is wrong: state it on `TangentSpace` directly and never through a `Fin 1`-form.

## 6. Rating

**L** for the recommended pair G1 + G6, P(success) medium, value high (the moment-map line). **XL** for
G5, queued (§9). `R-016′` **L**, medium, value medium, and it is a statement, not a discharge.
Nothing here has been "attempted and walled"; every absence above was a grep.

## 8. Additions after G1 and G6 (2026-09-08, late): G8–G13

The remaining "not established" lines of `TERMS.md` and `POSITS.md`, each as a numbered brick. Every
shelf claim was grep-probed at the pin on 2026-09-08. These IDs supersede the chat-only labels used
earlier the same evening.

| # | Brick | Cx | P(success) | Value | What it lands, honestly |
|---|---|---|---|---|---|
| **G8** | **A moment map is unique up to a constant, and the normalisation pins it.** (A) On `ℂℙⁿ`, two `MDifferentiable` Hamiltonians `H, K` of the same field for the same 2-form family differ by a constant. (B) If `Hₖ` is a Hamiltonian for the `k`-th phase field `torusField (Pi.single k 1)`, `Hₖ ≥ 0`, and `∑ₖ Hₖ = 2` (the form's scale), then `Hₖ = torusHamiltonian (Pi.single k 1) = 2 · momentMap · k`. | **M** | High | **High** (ledgers) | The sentence `POSITS.md` bullet 1 calls "the standard symplectic argument, unformalised" becomes a theorem, given G6. **Posit 1 is unchanged**: it asserts that the *dynamics* generates the torus action; G8 only says the map that action has is the corpus's. Appends to `Instances/ProjectiveSpaceMomentMap.lean` (no new file). |
| **G9** ✅ built 2026-09-09 | The image of `momentMap` is exactly the standard simplex | S–M | High | Medium | `momentMap_sum_eq_one` and `momentMap_nonneg` give `⊆`; `⊇` by exhibiting `mk (fun k => √tₖ)`. Closes the "moment polytope" line for this action, without the convexity theorem. |
| **G10** ✅ built 2026-09-09 | The torus flow preserves the Fubini–Study volume: `Measure.map (torusUnitary θ • ·) (fsVolume n) = fsVolume n` | S | High | Medium | A one-line corollary of `fsVolume_map_smul`. Liouville in the dynamics sense for the flow G6 built, without G5. |
| **G11** ✅ built 2026-09-09 | Hamiltonian implies locally Hamiltonian | M | High | Low–medium | `mextDeriv` of a 0-form family is `mfderiv` (flat half upstream: `extDeriv_constOfIsEmpty`) plus smoothness of the 0-form section and `d ∘ d = 0`. |
| **G12** ✅ built 2026-09-10 | `fsForm` is analytic, not merely `C^∞` | M–L (was **S**) | Medium | Low | Real-analyticity of `log(1 + ‖z‖²)` — `Kahler.contDiff_omega_fsPotential`, the `C^∞` proof at `ω` — pushed through `d^c`, `dd^c`, the pullback and the chart, every step of which was already generic in the order: ★★ `contMDiff_omega_fsForm` (**the Fubini–Study form is an analytic section**) and `fsFormAnalytic`, the section as a term of the `ω` type. The "registry line" turned out to be an S brick; see §G12. |
| **G13** ✅ built 2026-09-09 | The `U(n+1)` moment map `⟨z, iAz⟩/‖z‖²` for a general skew-Hermitian `A` — built as: the Schrödinger flow `exp(-itH)` is Hamiltonian with Hamiltonian `-2 ⟨H⟩`, `A = -iH` | M–L | Medium | Low–medium | The G6 computation with a non-diagonal velocity; the corpus uses the torus. |

### G8, planned

**Route for (A).** No connectedness lemma is needed. (i) From `α x (X x, v) = dH v = dK v` for all `v`,
`mfderiv H x = mfderiv K x` (CLM extensionality), so `mfderiv (H − K) x = 0` (`mfderiv_sub`). (ii) In
the affine chart `i`, `mfderiv` is the chart derivative — the bridge G6 built in
`hasMFDerivAt_torusHamiltonian` (`MDifferentiableAt.mfderiv`, `writtenInExtChartAt`,
`extChartAt_model_space_eq_id`, `extChartAt_coe_symm`, `modelWithCornersSelf_coe_symm`) — so
`fderiv ℝ ((H − K) ∘ chartInv i) w = 0` for every `w`, and `(H − K) ∘ chartInv i` is differentiable
(`MDifferentiableAt` in the chart). (iii) The chart image is all of `Fin n → ℂ`, a normed space, so
Mathlib's `is_const_of_fderiv_eq_zero` (grep-confirmed, `Analysis/Calculus/MeanValue.lean`) makes
`(H − K) ∘ chartInv i` constant, hence `H − K` constant on `chartSource i` (`chartInv_chartFun`).
(iv) Glue: `mk (fun _ => 1)` lies in every `chartSource i` (`mem_chartSource_mk`, `1 ≠ 0`), so the
constants agree across charts and `c := (H − K) (mk 1)` works at every `p` through `chartSource (idx p)`.

**Route for (B).** By (A) and G6's `torusField_isHamiltonianVectorField (Pi.single k 1)`, with
`torusHamiltonian (Pi.single k 1) p = 2 · momentMap p k` (`Finset.sum_ite_eq`), `Hₖ = 2μₖ + cₖ`. Summing
and `momentMap_sum_eq_one`: `∑ cₖ = 0`. Non-negativity at a point where `μₖ = 0`: for `n ≥ 1` and
`j ≠ k`, `momentMap (origin j) k = 0` (from `rep_origin`; a new S lemma), so `cₖ ≥ 0`; then
`Finset.sum_eq_zero_iff_of_nonneg` gives `cₖ = 0`. For `n = 0` the sum has one term, so `c₀ = 0`
directly.

**Generic piece for G1's module:** `IsHamiltonianVectorField.mfderiv_eq` — two Hamiltonians of the
same field for the same form have the same `mfderiv` at every point (S; `HamiltonianVectorField.lean`).

**Deliverable and pins.** Appended to `Instances/ProjectiveSpaceMomentMap.lean` (capstone discipline,
CONVENTIONS §8.3b): `momentMap_origin_of_ne`, `torusHamiltonian_single`,
★★ `eq_add_const_of_isHamiltonianVectorField` (A), ★★★ `eq_torusHamiltonian_of_nonneg_of_sum` (B);
plus `IsHamiltonianVectorField.mfderiv_eq` in G1's module. Names carrying "Hamiltonian" go into
`check-claims.sh`'s theorem inventory. Docs: `POSITS.md` bullet 1 (the argument is formalised; the
posit stands), `TERMS.md` moment map, this note, BACKLOG.

**⛔ Stop condition.** If step (ii) needs more than the G6 bridge — if `MDifferentiableAt.mfderiv`
does not hand over the chart derivative on `Fin n → ℂ` in the form `is_const_of_fderiv_eq_zero`
takes — state (A) with `HasMFDerivAt` hypotheses instead of `MDifferentiable` and stop there; do not
build a manifold-level constancy lemma for one consumer.

**Rating: M, P(success) high, value high for the ledgers and nil for the posit count.**

### G12, built (2026-09-10)

**What was expected.** The row was priced M–L and marked "registry line only": analyticity of the potential
`log(1 + ‖z‖²)` was assumed to need a real-analytic calculus the corpus had never touched, and the value is
low — nothing downstream consumes `ω`.

**What it took.** S. Mathlib's `ContDiff.log`, `contDiff_norm_sq`, `ContDiff.fderiv_right`,
`ContinuousLinearMap.contDiff`, `contMDiffAt_extChartAt`, `contMDiffAt_section` and the corpus's own
alternating-bundle instance are all generic in the order `n : WithTop ℕ∞`, and the manifold was already
`IsManifold 𝓘(ℝ, Fin n → ℂ) ω` (`instIsManifoldReal`). So the `C^∞` proofs of `contDiff_fsPotential`,
`contDiff_dcForm`, `contDiff_fsChartForm`, `contDiff_fsModelForm` and `contMDiffAt_fsSection` re-run verbatim at
`ω`, with `ω + 1 ≤ ω` discharged by `le_top` where the `∞` proofs used `by simp`. The `∞` lemmas are kept
(their consumers pass `(⊤ : ℕ∞)` through elaboration in a dozen places; generalising the statements to an
implicit order would have left metavariables at the `.contDiffAt.of_le` sites), and the `ω` lemmas are
`contDiff_omega_*` / `contMDiff_omega_*` alongside them.

**What it lands.** `Kahler.contDiff_omega_fsPotential`, `analyticAt_fsPotential`, `contDiff_omega_dcForm`
(`KahlerPotential.lean`); `fsChartForm_eq_alternatizeUncurryFinCLM_fderiv` (the shape both orders' proofs
use), `contDiff_omega_fsChartForm`, `contDiff_omega_fsModelForm`, `contMDiffAt_omega_fsSection`,
`contMDiff_omega_fsSection`, ★★ `contMDiff_omega_fsForm`, `fsFormAnalytic`, `fsFormAnalytic_apply`
(`Instances/ProjectiveSpaceFubiniStudyForm.lean`). 11 pins.

**What it does not do.** Nothing downstream is restated at `ω`: `IsSymplectic`, `IsAlmostKahler`, the
Hamiltonian layer and the top-power measure are all on the `∞` form `fsForm`, and `fsFormAnalytic` is the same
section (`fsFormAnalytic_apply` is `rfl`), not a second object with its own theory. Analyticity of the
Hamiltonian vector fields (`torusField`, `schrodingerField`) would follow the G3 route at `ω` and is not
written.

### G14a, built (2026-09-10)

**What.** `DifferentialForm.IsKahler β J J₀` (`HamiltonianVectorField.lean`): `IsAlmostKahler β J` plus one
field, `J_symmL` — `J` is the model's complex structure `J₀ : E →L[ℝ] E` through the tangent trivialisation
of every chart. That single field is integrability *in the atlas sense*: ★ `IsKahler.apply_eq` (`J y = J₀` in
`y`'s own chart, from `tangent_symmL_eq_fderiv` at `x₀ = y` and the identity transition's derivative,
`fderiv_chart_transition_self`), ★ `IsKahler.fderiv_chart_transition_comm` (**every chart transition has
`J₀`-linear derivative** — the Cauchy–Riemann equations of the atlas, i.e. the atlas is holomorphic and `J` is
its complex structure), `IsKahler.J₀_J₀`; and `IsAlmostKahler.metric_J_J` (the metric is Hermitian). So
`IsKahler` is the textbook definition — a complex manifold with a Hermitian metric whose fundamental form is
closed. On `ℂℙⁿ`: `modelJ` (`i·` on `Fin n → ℂ` as a real-linear map, the `complexStructureL` pattern) and
★★★ `fsForm_isKahler` (`Instances/ProjectiveSpaceFubiniStudySymplectic.lean`), whose `J_symmL` is G7's
`fsJ_symmL` verbatim. **S**, as priced. 9 pins.

**Why one field.** A second field "every transition is holomorphic" would be redundant: with `J` a single
family, reading it as `J₀` in two charts at a common point forces the transition derivative to commute with
`J₀` — which is the proof of `fderiv_chart_transition_comm`. One shelf fact, the G7 trap again: after
`rw [tangent_symmL_eq_fderiv]` the identity CLM sits on the `TangentSpace` instance path, so
`ContinuousLinearMap.id_apply` and `rw [h.apply_eq]` both fail "not type-correct under implicit
transparency"; finish with `exact h1` (defeq) and `h1.symm.trans (h.apply_eq y _)`.

**What it does not do.** The tensor form — the Nijenhuis tensor `N_J(X, Y) = [JX, JY] − J[JX, Y] − J[X, JY]
− [X, Y]` vanishes — is not stated (G14b); `J` is a family of maps, not a smooth section of the
endomorphism bundle (G15). Nothing in `LF4` consumes `IsKahler` yet (W1).

## 9. The residue, every item priced (2026-09-10)

**Policy (the author's, 2026-09-10).** No row is "not scheduled". Every residue of the ladder is a numbered,
priced row here, and the author decides when it is built; work that Mathlib later lands is deprecated in
favour of Mathlib's version. Prices are honest — an XL is an XL — but a price is information, not a verdict.
Every shelf claim below was grep-probed at the pin on 2026-09-10; note that two absences the earlier sections
recorded have since been filled upstream (`VectorField.mlieBracket`, and uniform-time global integral curves
`exists_isMIntegralCurve_of_isMIntegralCurveOn`).

| # | Brick | Cx | P(success) | Value | What it lands, honestly — and the Mathlib gap it fills |
|---|---|---|---|---|---|
| **G5** ✅ built 2026-09-11/12 (as Q29 (a), (a′), (b′), (c′), (d′) on the chart route, §11) | **Liouville at manifold level**: the time-`t` map of `X_H` preserves `topFormMeasure (ω^{∧n})`. Three milestones. **(a)** the global flow of a `C^1` vector field on a compact manifold — global integral curves exist (`exists_isMIntegralCurve_of_isMIntegralCurveOn` at the pin gives them from a uniform local existence time; compactness supplies the uniform time), are unique (G4), and assemble into a `Flow` (`Mathlib/Dynamics/Flow.lean`); **(b)** the Lie derivative of a manifold form along the flow and Cartan's formula `L_X = d ∘ ι_X + ι_X ∘ d` — the genuine Mathlib gap (no `lieDeriv`, no Cartan at the pin; needs pullback of `DifferentialForm` along a smooth map and `mextDeriv` commuting with it); **(c)** `L_X ω = d(ι_X ω) = d(dH) = 0` (G11's `isLocallyHamiltonian` is exactly `d(ι_X ω) = 0`), so the flow preserves `ω`, hence `ω^{∧n}`, hence `topFormMeasure` (`topFormMeasure_map_eq`). | (a) **M–L**, (b) **L–XL**, (c) **M**; **XL** in all | Low–medium | Medium | Replaces `ConstraintDynamics.flow_preserves` by a theorem for the globally Hamiltonian pieces only; the measurement pieces are locally Hamiltonian (the flux correction), so Posit 3 stands even then. |
| **G14a** ✅ built 2026-09-10 | The Kähler predicate, atlas sense; `ℂℙⁿ` is Kähler | S–M (took **S**) | — | Medium | See §G14a above. |
| **G14b** ✅ built 2026-09-10 | **Kähler in the tensor sense**: the Nijenhuis tensor `N_J` of a family `J` via `VectorField.mlieBracket` (at the pin), and `N_J = 0` for `IsKahler` — the easy direction of Newlander–Nirenberg (a holomorphic atlas makes `N_J` vanish, a chart computation: in a chart `J = J₀` is constant, and the bracket of coordinate-constant fields is `0`). The converse (`N_J = 0` ⇒ holomorphic atlas) is the hard PDE theorem and is **not** this row. | **M–L** | Medium | Low | Closes the `TERMS.md` "tensor sense" line; `IsKahler.nijenhuis_eq_zero`. Needs `J` as a section (G15) to state `[JX, JY]`. |
| **G15** ✅ built 2026-09-10 | **`J` as a smooth section of `End(TM)`**: `fun x => (x, fsJ x)` is `C^∞` into the bundle of continuous linear maps `TangentSpace x →L[ℝ] TangentSpace x` (`Mathlib/Geometry/Manifold/VectorBundle/Hom.lean` at the pin); generically, `IsKahler` implies the section is `C^∞` because `J` is constant in every chart. | **S–M** | High | Low | The `TERMS.md` "smooth section" line; prerequisite of G14b. |
| **G16** ✅ built 2026-09-10 | **The torus orbits are integral curves**: `t ↦ torusUnitary (t • θ) • p` is `IsMIntegralCurve` for `torusField θ`, and `momentMap` is conserved along it. | **S** | High | Low | The route of `isMIntegralCurve_schrodingerUnitary_smul` with `hasDerivAt_chartFun_torusUnitary` and `torusUnitary_add_smul`; the G4 write-up left it unwritten. |
| **G17** ✅ built 2026-09-11 | **The Riemannian volume of the Fubini–Study metric is `fsVolume` up to the constant** (the `TERMS.md` Fubini–Study line "normalised Riemannian volume"). Needs the Riemannian volume measure of a metric on a manifold — absent at the pin (`VectorBundle/Riemannian.lean` has Riemannian *bundles*, no volume) — built as `topFormMeasure` of the volume form `√det g`; then `vol_g = ω^{∧n}/n!` is the algebraic Kähler identity from `g = ω (J ·, ·)` (G14a). | **L** | Low–medium | Low | Fills a Mathlib gap (Riemannian volume); nothing in the corpus consumes it. |
| **G17b** ✅ built 2026-09-11 (Q30) | **Chart-independence of the Riemannian volume**: `√det (DφᵀGDφ) = \|det Dφ\| √det G` along a chart transition, then `MetricFamily.chartMeasure_congr` by the proof of `DifferentialForm.chartMeasure_congr` with the Jacobian rule for Gram matrices in place of the one for top-form coefficients; then `riemannianVolume_congr_cover`. | **S–M** | High | Low | Makes `riemannianVolume` canonical for a metric not identified chart by chart with a top form; nothing in the corpus needs it (on `ℂℙⁿ` independence is inherited from `topFormMeasure_congr_cover`). |
| **G18** | **Darboux's theorem** (the `TERMS.md` symplectic line): every symplectic form is locally the standard one. Moser's trick: needs G5(a) flows, G5(b) Cartan, and a Poincaré lemma on a ball. | **XL** | Low | Low | Nothing in the corpus consumes it; it is the classical theorem a symplectic library owes. |
| **W1** ✅ built 2026-09-10 | **Wire the physics to the manifold layer**: the `ℂℙⁿ` instances of `KahlerOnticSetup` (`trivialKahlerOnticSetup`, `unitaryFlowSetup`, `manyToOneSetup`) get theorems that their `liouvilleMeasure` is `(4π)⁻ⁿ • fsVolume n` (the symplectic volume of `fsForm`, `fsVolume_eq_smul_fubiniStudyMeasure`), that `flow_preserves_volume` is `fsVolume_map_smul`, and that the sector carries `fsForm_isKahler`; and the four stale ledgers are corrected — link L1 of `specs/connectivity-manifest.md`, the `kahler_pointwise` docstring, and the `TERMS.md` Fubini–Study and symplectic entries, all of which still call the manifold residual open. The two projective-space types are definitionally equal (`ℙ ℂ (Ambient n)` is `CPN (n + 1)`). | **M** | High | **High** | This is what turns "we start from an FS, Kähler, Liouville space" into "the sector is the standard object, proved". Posit 3 is untouched by it. |
| **G19** ✅ built 2026-09-10 | Analyticity of the Hamiltonian fields: `torusField`, `schrodingerField` are `ω` sections (the G3 route at `ω`; `hamiltonianVectorFieldSection` is `C^ω` for a `C^ω` form and energy). | **S–M** | High | Low | The G12 write-up left it unwritten. |

### W1, built (2026-09-10)

**What.** New module `LF4/SectorManifold.lean` (imports `LF4/KahlerVolumeForced.lean` and the Mass and
Symplectic instance modules; the manifold tree imports nothing from `LF4` except the two moment-map
modules, so no cycle). For the `ℂℙⁿ` instances of `KahlerOnticSetup` at `N = n + 1`: ★★★
`unitaryFlowSetup_liouvilleMeasure_eq_fsVolumeNormalized` and the `trivialKahlerOnticSetup` twin
(`liouvilleMeasure = fsVolumeNormalized n`, by `fsVolumeNormalized_eq_fubiniStudyMeasure`), ★★
`fsVolume_eq_smul_unitaryFlowSetup_liouvilleMeasure` (the `(4π)ⁿ`), ★★
`unitaryFlowSetup_flow_measurePreserving_fsVolume` (every time-`t` map preserves `fsVolume n` itself:
`fsVolume_map_smul`), ★★★ `fsVolumeNormalized_isForcedKahlerVolume` (the normalised top power satisfies
`IsForcedKahlerVolume`, so the `LF4` symmetry characterisation and the manifold layer's Kähler-form
characterisation pin the same measure), the three many-to-one facts (`kMuL = fsVolumeNormalized n ⊗ Haar`,
base marginal, flow preserves `fsVolume n ⊗ Haar`), and ★★★ `unitaryFlowSetup_isKahler_liouville` /
`manyToOneSetup_isKahler_liouville` — Kähler target (`fsForm_isKahler`) ∧ Liouville = normalised top power
∧ flow preserves it. **M** as priced; took S–M. 10 pins.

**What it corrects.** The stale set was larger than the four ledgers the row named: `KahlerOnticSetup.lean`
(two docstrings), `KahlerVolumeForced.lean`, `LiouvilleUnique.lean`, `ManyToOnePillars.lean`,
`NonTrivialSetup.lean`, `connectivity-manifest.md` (L1 DISCHARGED, three spots), `reconstruction-status.md`
(A1, L1), `future-work.md` (KG-1 DONE), `TERMS.md` (Fubini–Study and symplectic entries, Kähler and
Liouville entries extended), `README.md` (the "no symplectic manifold is built" non-claim replaced by the
honest residual: Liouville for a general Hamiltonian flow), `docs/TOUR.md` (the Kähler row, and the
propagator's reason). The `MATHLIB-ABSENT` sentinel in `KahlerVolumeForced.lean` is kept: Mathlib still has
no manifold differential forms at the pin; the corpus has its own.

**What it does not do.** `KahlerOnticSetup` is unchanged — its fields are still posited for an abstract `Σ`;
this module proves the `ℂℙⁿ` instances' posited data *are* the standard objects. The pointwise field
`kahler_pointwise` (ambient `ℂ^{N}`) and the manifold predicate `fsForm_isKahler` (the target `ℂℙⁿ`,
tangent model `ℂⁿ`) are on different spaces and no implication is stated. Posit 3 stands: the flows here
are unitary. Two shelf facts: a theorem stated on `(setup).flow t` cannot be reused in a `MeasurePreserving.prod`
— the `SFinite` instance search runs on the setup's bundled `instMeasurable` projection, which is opaque
to instance-reducible unfolding — so state the base factor on `CPN (n + 1)` directly; and `ℙ` needs
`open scoped LinearAlgebra.Projectivization`, which `LF4` modules replace by the abbrev `CPN`.

### G15 and G16, built (2026-09-10)

**G15.** ★★ `DifferentialForm.IsKahler.contMDiff_hom_section` (`HamiltonianVectorField.lean`, now
importing `Mathlib/Geometry/Manifold/VectorBundle/Hom.lean`): for a Kähler structure whose `J` is supplied
as continuous linear maps `JL` (`JL x v = J x v`), the section `x ↦ JL x` of `Hom(TM, TM)` is `C^∞`. Proof:
`contMDiffAt_section` on the Hom bundle, whose trivialisation at `x₀` reads a section as
`continuousLinearMapAt y ∘ JL y ∘ symmL y` (`hom_trivializationAt`, `continuousLinearMap_apply`, both
`rfl`); by `J_symmL` and `continuousLinearMapAt_symmL` that is the constant `J₀` on the chart source, so
`contMDiffAt_const.congr_of_eventuallyEq`. On `ℂℙⁿ`: `fsJL x := modelJ` (the linear-map version of
`fsJ`, `fsJL_apply` is `rfl`) and ★★ `contMDiff_fsJL`. **S–M** as priced; took S. Compiled first try.

**G16.** In `Instances/ProjectiveSpaceSchrodingerFlow.lean`, where the torus corollaries of G2/G3
already live: `continuous_torusUnitary_smul` (`Continuous.matrix_diagonal` on `torusUnitary_val`), ★★★
`isMIntegralCurve_torusUnitary_smul` — the G4 proof of `isMIntegralCurve_schrodingerUnitary_smul` with
`hasDerivAt_chartFun_torusUnitary` and `torusUnitary_add_smul`, plus one `show` to unfold the
cross-module `torusField` at the derivative — `isMIntegralCurve_torusField_eq`, ★★
`eq_torusUnitary_smul_of_isMIntegralCurve` (every global integral curve through `p` at `0` IS the orbit),
★★ `torusHamiltonian_eq_of_isMIntegralCurve_torusField` and ★★ `torusHamiltonian_torusUnitary_smul`
(`2 ∑ θₖ μₖ` conserved along the curves and by the flow). **S** as priced. 10 pins for the pair.

**What they do not do.** G15 is stated for a `J` given as linear maps; the predicate's `J` stays a family
of functions (packaging `J` as linear maps inside `IsKahler` would change G14a's structure for no
consumer). G16 conserves the torus Hamiltonian, not each `μₖ` separately along the flow of a general `θ`
(true, by the diagonal action; not written). Neither touches G5.

### G19, built (2026-09-10)

**What.** G3's chain at `ω`. `ExteriorDerivative.lean`: ★ `contDiffAt_omega_localRep` (a `C^ω` section has
`C^ω` local representatives; the `∞` proof with `contMDiffOn_chart_symm (n := ω)`, on an analytic
manifold). `HamiltonianVectorField.lean`, new section `SmoothAnalytic` with `[IsManifold 𝓘(ℝ, E) ω M]`:
`ofOmega` (a `C^ω` 2-form read as the `C^∞` form G2/G3's constructions are typed on — `⟨α, α.contMDiff_toFun.of_le
le_top⟩`, so `ofOmega α x = α x` is `rfl`), ★★ `contDiffAt_omega_localHamiltonianVector` (the `∞` proof at `ω`:
`IsBoundedLinearMap.contDiff`, `contDiffAt_map_inverse`, `ContDiffAt.clm_apply` and `fderiv_right` are all
generic in the order; `ω + 1 ≤ ω` is `le_top`), ★★★ `contMDiff_omega_hamiltonianVectorField` (**the
Hamiltonian vector field of a `C^ω` energy for a `C^ω` non-degenerate 2-form is a `C^ω` section**), reusing
G3's pointwise identity `trivializationAt_hamiltonianVectorField_snd` on `ofOmega α` with `hH.of_le le_top`.
On `ℂℙⁿ` (`ProjectiveSpaceSchrodingerFlow.lean`): `contDiff_omega_schrodingerChartHam` (the inner-product
calculus is order-generic), ★ `contMDiff_omega_schrodingerHamiltonian`, ★ `contMDiff_omega_torusHamiltonian`,
★★ `contMDiff_omega_schrodingerField`, ★★ `contMDiff_omega_torusField` — for the analytic form
`fsFormAnalytic` of G12, whose family is `fsForm`'s definitionally. **S–M** as priced; took S. 10 pins.

**Two shelf facts.** `omit [IsManifold 𝓘(ℝ, E) ∞ M] in` is refused ("cannot omit referenced section
variable") on anything mentioning `localRep` or `localHamiltonianVector`, because those defs carry the `∞`
instance; so the `ω` section keeps both instances and omits only on the `rfl` lemma. And the `∞`-typed API is
reused rather than duplicated: `ofOmega` is the one-line bridge, and `exact` crosses `ofOmega α x ≡ α x` and
`fsFormAnalytic x ≡ fsForm x` (both exposed defs) without help.

**What it does not do.** No `C^ω` twin of `hamiltonianVectorFieldSection` (no consumer); `IsSymplectic` stays
on the `∞` form, so the `ℂℙⁿ` statements take `(fsForm_isSymplectic n).nondegenerate` directly. The residue of
§9 is now G5, G14b, G17, G18.

### G14b, built (2026-09-10)

**What.** `DifferentialForm.nijenhuis J V W x := [JV, JW] − J[JV, W] − J[V, JW] − [V, W]` with Mathlib's
`VectorField.mlieBracket` (`HamiltonianVectorField.lean`, new section `Nijenhuis`; the module now imports
`Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`), and ★★★ `IsKahler.nijenhuis_eq_zero`: on a Kähler
manifold (atlas sense, G14a) the tensor vanishes on vector fields differentiable at the point. Proof, in the
chart at `x₀`: (i) `mlieBracketWithin_apply` is `rfl` and `mfderiv_extChartAt_self` makes the chart's derivative
the identity at its base point, so every manifold bracket at `x₀` IS the flat `lieBracket` of the two fields
pulled back along the inverse chart (`key`); (ii) the pullback of `J X` is `J₀ ∘` the pullback of `X` on the
whole chart target — `mpullback_extChartAt_symm_apply_J`, from `J_symmL` through Mathlib's
`TangentBundle.continuousLinearMapAt_trivializationAt` and the two chart-derivative composition identities
read via `ContinuousLinearMap.inverse_eq` (`inverse_mfderiv_extChartAt_symm`); (iii) the pullbacks are
differentiable at the base point (`MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField`),
so `D(J₀ ∘ X') = J₀ ∘ DX'`; (iv) the flat expression for a constant `J₀` with `J₀² = −1` cancels
(`flat_nijenhuis_eq_zero`, on `E`, by `abel`). On `ℂℙⁿ`: ★★ `nijenhuis_fsJ_eq_zero`. **M–L** as priced; took M.
7 pins.

**Three shelf facts.** (a) The chart pullbacks have the dependent type `(w : E) → TangentSpace 𝓘(ℝ, E) w`, and
`rw` cannot match them against `E → E` at reducible transparency — the reducible cast `flatField` (the
`toFlat` / `tangentToModel` idiom) is what makes the flat `lieBracket` API rewrite. (b) `abel` cannot merge
subtractions typed on the tangent-space instance path with ones typed on `E`: prove the cancellation as a
lemma on `E` and close with `exact`. (c) `ContinuousLinearMap.inverse_id` and `continuousLinearMapAt_symmL`
refuse to rewrite once a chart derivative has been swapped for a trivialisation map (the G7/G14a trap
again): finish with `exact`/`.trans`.

**What it does not do.** The converse of Newlander–Nirenberg (`N_J = 0` ⇒ holomorphic atlas), a genuine PDE
theorem, is not stated and nothing here needs it. `nijenhuis` takes the family `J`; the smooth-section
version (G15) is separate. The residue of §9 is now G5, G17, G18.

### G17, built (2026-09-11)

**What.** Two new modules. `Geometry/Manifold/RiemannianVolume.lean` (generic): for a metric family `g`
on a manifold, `MetricFamily.localRep g x₀ w u v` (the metric under the chart, on tangent vectors read
through `symmL`), `gram e g x₀ w` (its Gram matrix against a basis `e` of the model), `chartDensity =
ENNReal.ofReal √det`, `chartMeasure` (pushed to `M` by the chart), and ★★ `riemannianVolume μ e g c`
(glued along a `ChartCover`, the `TopFormMeasure` construction verbatim with the Gram density in place
of the top-form coefficient); ★★ `riemannianVolume_eq_smul_topFormMeasure` — if in every chart of the
cover the Gram density is `k` times a top form's coefficient density, the volume is `k` times the
top-form measure. `Instances/ProjectiveSpaceFubiniStudyRiemannian.lean`: `fsMetric = ω(J·,·)`
(rfl-equal to the almost Kähler metric), the model metric `fsModelMetric w` as a `BilinForm`,
★ `localRep_fsMetric` (in every chart the metric reads as the model metric: `fsJ_symmL` and a pointwise
form of `localRep_fsSection`, `fsForm_symmL_symmL`), ★★ `det_toMatrix_fsModelMetric` (the Gram
determinant is `(4ⁿ (1 + ‖w‖²)^{-(n+1)})²` — the `wedgePow_fsModelForm_stdBasis` route: rotate `w` to
the first axis by a unitary, whose real determinant is `1`; scale to the origin along `fsScale`,
`BilinForm.toMatrix_comp` and `LinearMap.det_toMatrix` giving `det² · det G₀`; at the origin the Gram
matrix is `4·1` because the standard basis is orthonormal for `Re⟪·,·⟫`, `stdBasis_inner_re`),
★★ `chartDensity_fsMetric` (`√det G = (1/n!) · |coeff of ω^{∧n}|`), ★★★ `riemannianVolume_fsMetric`
(**`vol_g = fsVolume n / n!`**) and ★★★ `riemannianVolume_fsMetric_eq_smul_fubiniStudyMeasure`
(**`vol_g = ((4π)ⁿ/n!) · μ_FS`**). **L** as priced; took M–L. 27 pins.

**Three shelf facts.** (a) `LinearMap.BilinForm.toMatrix_comp` must be given both bases and both maps
explicitly, else its index type's `DecidableEq` is stuck. (b) `mulVecCLM` from the Mass module lives in
`(Fin n → ℂ) →L[ℝ] _` and its `n` is not inferred from `fsScale`'s type — wrap it as the `→ₗ` map
`mulVecL` with `det_mulVecL`. (c) `∞` is ambiguous between `ℝ≥0∞` and `ℕ∞ω` once both scopes are open —
write `⊤` for the extended-real one.

**What it does not do.** Chart-independence of the Gram-density construction for a general metric is
**G17b** (S–M: `√det (DφᵀGDφ) = |det Dφ| √det G` along a transition, then the `chartMeasure_congr` proof
with the Jacobian in place of the top-form rule); on `ℂℙⁿ` it is inherited from the top-form side.
No orientation is chosen, so `vol_g = ω^{∧n}/n!` is an identity of measures, not of forms. The residue
of §9 is now G5, G17b, G18.

## 10. What the G series achieved, in plain terms (2026-09-11)

**The question it answers.** Paper C describes the ontic arena as a compact Kähler manifold with
its symplectic volume as the typicality measure and a Hamiltonian flow on it. Until September 2026
the Lean corpus *used* those words but did not *build* those objects: the state space was a
`Projectivization` type with a measure defined by symmetry, the "Kähler" field was a pointwise
identity on flat vectors, and "Liouville", "moment map" and "Hamiltonian" were names attached to
posited structure fields. The corpus was honest about this (the `TERMS.md` restricted senses, the
`TERM-SCOPE` markers, connectivity link L1 "PARTIAL"), but a reader could fairly ask whether CSD was
resting on mathematics it had proved or on mathematics it had named.

**What is now proved, layer by layer.** Every item is a Lean theorem with an axiom pin; none is a
posit.

1. *The arena is a manifold.* `ℂℙⁿ` is an analytic manifold with the affine charts as its atlas
   (step 0). Not assumed — the chart transitions are proved holomorphic.
2. *The Fubini–Study form is a genuine differential form on it.* Built from the potential
   `log(1 + ‖z‖²)` chart by chart, proved to glue (chart invariance), proved smooth, then analytic
   (G12). Closed (`dω = 0`, step 2b) and non-degenerate: **`ℂℙⁿ` is a symplectic manifold** (step 4a).
3. *It is Kähler, in both textbook senses.* With `J = i·`: almost Kähler (G7); the complex
   structure of a holomorphic atlas (G14a); Nijenhuis tensor zero (G14b); `J` a smooth section of the
   endomorphism bundle (G15). The compatible metric is the Fubini–Study metric.
4. *Its volume is what the physics said it was — three ways, all the same measure.* The
   Fubini–Study measure had been *defined* as the unique unitary-invariant probability measure. It
   is now *proved* to equal the normalised top power `ω^{∧n}` of the Kähler form, with the constant
   `(4π)ⁿ` visible (step 3, M7), and the normalised Riemannian volume of the Fubini–Study metric,
   with `ω^{∧n}/n!` (G17). The measure theory this needed — a measure from a top form on a manifold,
   and a Riemannian volume — did not exist in Mathlib and was built here.
5. *The dynamics is Hamiltonian, as a theorem.* The defining equation `ι_X ω = dH` is stated on the
   manifold (G1). For every Hermitian `H`, the Schrödinger flow `exp(-itH)` on `ℂℙⁿ` is the flow of
   the Hamiltonian vector field of `−2⟨H⟩` (G13), that field exists, is unique, smooth and analytic
   (G2, G3, G19), the flow is literally its integral curve (G4), and `⟨H⟩` is conserved along it.
   The torus action is the diagonal case, with `2 ∑ θₖ μₖ` as Hamiltonian (G6): **the moment map
   is a moment map**, unique up to a constant, pinned by the normalisation (G8), with image exactly
   the simplex (G9); its orbits are the integral curves (G16). Every time-`t` map preserves the
   symplectic volume (G10, W1), and both flows ARE the manifold Hamiltonian flows of their
   Hamiltonians, preserving the volume by Liouville's theorem (Q29(d′), (e)).
6. *The physics layer cites all of it.* The abstract sector structure `KahlerOnticSetup` is
   unchanged, but its `ℂℙⁿ` instances now come with theorems that their posited Liouville measure IS
   the symplectic volume and their posited preservation IS the invariance of that volume (W1,
   `LF4/SectorManifold.lean`) — and, for the Schrödinger sectors, IS Liouville's theorem for the
   Hamiltonian flow of `−2⟨H⟩` (Q29(e), the `_derived` twins); connectivity link L1 is discharged;
   the glossary and the landing surface say so.

**So: is CSD grounded in proven mathematics rather than in naming?** For the *geometry of the
sector* — yes, now. The words symplectic, Kähler, Fubini–Study volume, Liouville measure (for the
unitary flows), moment map, Hamiltonian vector field, and integral curve all name objects that are
constructed and theorems that are proved, on the manifold the paper means, from Mathlib's
foundations plus the corpus's own staged manifold layer, with zero imported axioms beyond the
foundational triple.

**What it did not change, said plainly.** The G series builds the arena's geometry; it does not
derive the arena. Three things remain posits, exactly as before:
* *Posit 2, the sector itself* — that the ontic typicality measure is Fubini–Study. The geometry is
  now proved to *agree* with the symmetry argument that carries the Born derivation; it does not
  replace it, and the sector is still posited and constrained, not derived.
* *Posit 3, Liouville for the constraint dynamics* — proved for the unitary flows by invariance,
  and (2026-09-12, Q29(d′)) for every smooth Hamiltonian flow on `ℂℙⁿ` by the manifold-level
  Liouville theorem; the measurement pieces are only locally Hamiltonian, so the posit stands.
* *Posit 1, the cell law* — that the dynamics generates the torus action. G6/G8 show the map that
  action *has* is the corpus's moment map; they do not show the dynamics produces the action.

And two theorem-shaped residues on the ladder itself: Darboux (G18) and the chart-independence of
the generic Riemannian-volume construction (G17b), neither consumed by the physics.

**How to cite this.** The one-line version for a referee: *the sector's Kähler geometry, its
symplectic volume, and the Hamiltonian character of its unitary flows are theorems on `ℂℙⁿ`
(`fsForm_isKahler`, `fsVolume_eq_smul_fubiniStudyMeasure`, `riemannianVolume_fsMetric`,
`schrodingerField_isHamiltonianVectorField`), and the corpus's sector instances are proved to carry
them (`unitaryFlowSetup_isKahler_liouville`); the sector's *selection* remains a posit.*

## 11. The next pieces, priced with the evidence (2026-09-11)

Every ingredient below was grep-probed at the Mathlib pin on 2026-09-11; "absent" means the grep
found nothing, "present" names the declaration. Prices are honest; the author decides (§9 policy).
Rows are the `Q`-ids of `BACKLOG.md` ▶ OUTSTANDING with their `G`-ids in brackets.

### Q29 (= G5): Liouville at manifold level — `XL`, but the route has changed — **BUILT 2026-09-11/12, (a)–(d′)**

**What it would prove.** Every time-`t` map of the flow of a Hamiltonian vector field preserves
the symplectic volume `topFormMeasure (ω^{∧n})`. Today this is proved for the unitary flows on `ℂℙⁿ`
(W1, by invariance), and posited for the constraint dynamics (Posit 3).

**The route §9 priced (Cartan).** (a) global flows; (b) `L_X ω = d ι_X ω + ι_X dω` on a manifold;
(c) `L_X ω = 0` from G11. Milestone (b) is a Lie derivative of manifold forms, which is absent at the
pin (no `lieDeriv`, no Cartan anywhere under `Mathlib/Geometry/Manifold/` or
`Analysis/Calculus/DifferentialForm/`), and it is the reason for the XL.

**The route the corpus's own infrastructure suggests (chart-level ODE), found 2026-09-11.**
`topFormMeasure_map_eq` (`TopFormMeasure.lean`) already proves that a homeomorphism `g` preserves the
measure of a top form *given a chart-level pullback identity* `hinv`: in every chart, the local
representative pulled back along the chart expression of `g` equals the local representative. So
Liouville reduces to proving that identity for `g = φ_t`, which is a **flat** statement about the
chart flow `Φ_t := chart ∘ φ_t ∘ chart⁻¹` on an open set of `E`: `(Φ_t)^* ω_loc = ω_loc`. That is the
flat Liouville theorem, provable by the ODE `d/dt [(Φ_t)^* ω_loc] = (Φ_t)^* [L_X ω_loc]` where the
flat Lie derivative is `L_X ω = D_X ω + ω(DX ·, ·) + ω(·, DX ·)` — no manifold Lie derivative, no
manifold Cartan. The flat Cartan formula for a 2-form on a normed space is a finite identity of
alternating maps once `extDeriv_apply` is unfolded (`Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`,
present). Milestones on this route:

| | Milestone | Cx | Evidence at the pin |
|---|---|---|---|
| (a) | **Global flow of a `C^1` field on a compact manifold**: from `exists_isMIntegralCurve_of_isMIntegralCurveOn` (present, `IntegralCurve/UniformTime.lean`; needs a uniform `ε` — on a compact manifold the local existence time of `exists_isMIntegralCurveAt_of_contMDiffAt` is bounded below by compactness, a Lebesgue-number argument) and G4's uniqueness, assemble `φ : ℝ → M → M` with `φ (s+t) = φ s ∘ φ t` (`Mathlib/Dynamics/Flow.lean`, `structure Flow`, present) and each `φ t` a homeomorphism (`Flow.toHomeomorph`, present). | **M–L** | Both Mathlib halves present; the compactness step is the work. |
| (b′) | **Flat Liouville**: on an open `U ⊆ E`, for `X` `C^1` and `ω_loc` a `C^1` 2-form with the flat `L_X ω_loc = 0`, the flow `Φ_t` of `X` satisfies `(Φ_t)^* ω_loc = ω_loc` on its domain. Proof: fix `u, v`; `f(t) := ω_loc (Φ_t x) (DΦ_t u, DΦ_t v)` has `f' = 0` by the product rule and the variational equation `d/dt DΦ_t = DX ∘ DΦ_t`; `is_const_of_deriv_eq_zero`. The variational equation needs smooth dependence of the flow on initial data, which is **absent** at the pin (`Mathlib/Analysis/ODE/PicardLindelof.lean` gives existence and uniqueness only) — this is the genuine gap on this route, smaller than Cartan but real. | **L** | `is_const_of_deriv_eq_zero` present; smooth dependence on initial data absent. |
| (c′) | **`L_X ω = 0` for a Hamiltonian field, flat**: `L_X ω = d(ι_X ω) + ι_X dω` is the flat Cartan identity (a `Fin 2`-alternating-map computation from `extDeriv_apply`, present) and both terms vanish: `d(ι_X ω) = d(dH) = 0` (`extDeriv_extDeriv`, present; G11 gives the manifold form) and `dω = 0` (`fsForm_mextDeriv` read in the chart, `toFlat_mextDeriv`). | **M** | All present. |
| (d′) | **Assembly on `ℂℙⁿ`**: (a) gives `φ_t` as homeomorphisms; (b′)+(c′) in each chart give `hinv` for `topFormMeasure_map_eq`; conclude `Measure.map (φ_t) (fsVolume n) = fsVolume n` for every `C^∞` Hamiltonian `H`. Then `flow_preserves_volume` of `KahlerOnticSetup` is a theorem for every Hamiltonian flow, not only the unitary ones. | **M** | `topFormMeasure_map_eq` present in-corpus. |

**Re-price:** **L–XL** on the chart route (was XL on the Cartan route), with the smooth dependence
on initial data in (b′) the one Mathlib gap, itself an L. **Value: medium.** It would make Posit 3 a
theorem *for the globally Hamiltonian pieces of the constraint dynamics*; the measurement pieces are
only locally Hamiltonian (`RecordLayer/PiecewiseHamiltonian.lean`), so Posit 3 stands regardless
(`POSITS.md`). **P(success): medium.** Milestone (a) alone is a self-contained M–L with its own
payoff: global flows on compact manifolds, a Mathlib gap.

**Q29(a) BUILT 2026-09-11 (M–L as priced, took M).** `IntegralCurve/GlobalFlow.lean`. The pricing note
above said the compactness step was "the work"; it was, and the shape is worth recording. Mathlib's local
theorem hides the existence interval inside `IsMIntegralCurveAt`'s `∀ᶠ`, and its proof confines the chart
solution to the chart's target by continuity *at the one initial point*. For a uniform `ε` on a ball of
initial points the confinement must be uniform too. Two Mathlib facts make it so without continuous
dependence: `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` (one `ε` for a
closed ball of initial points — the "ball" version of Picard–Lindelöf, present), and the Picard structure's
own `mul_max_le : L·ε ≤ a − r`, which confines every solution to `closedBall x₀ a`
(`ODE.FunSpace.compProj_mem_closedBall`, public). So: rebuild Mathlib's `IsPicardLindelof.of_contDiffAt_one`
with the Lipschitz ball intersected with a prescribed neighbourhood (`ContDiffAt.isPicardLindelof_subset`),
restate `exists_eq_forall_mem_Icc_hasDerivWithinAt` with the confinement conclusion, take the prescribed
neighbourhood to be `interior (extChartAt x₀).target`, and Mathlib's own manifold-transport proof goes
through verbatim with `hf3 t` in place of its neighbourhood argument
(`exists_nhds_forall_exists_isMIntegralCurveOn_Ioo`). Then `CompactSpace.elim_nhds_subcover`, `Finset.inf'`,
and `exists_isMIntegralCurve_of_isMIntegralCurveOn`. The flow: `integralFlow` by `choose`, group law from
`IsMIntegralCurve.comp_add` + uniqueness. **Also found:** Mathlib HAS Lipschitz (hence continuous) dependence
of the local flow on the initial point (`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`),
so joint continuity of `integralFlow` — Q29(a′) — is S–M (glue along the cover), and what (b′) genuinely
lacks is *differentiable* dependence, the variational equation. 12 pins.

**Q29(a′) BUILT 2026-09-12 (S–M as priced, took M).** `IntegralCurve/FlowContinuity.lean`, 8 pins,
★★ `continuous_integralFlow : Continuous fun p : ℝ × M => integralFlow hv p.1 p.2`. The glue was not
"along the cover" but along the *group law*: (i) Mathlib's Lipschitz Picard–Lindelöf restated with the
confinement conjunct (`…_lipschitzOnWith_mem`), (ii) a jointly continuous local flow in the chart
(`ContDiffAt.exists_localFlow`: Lipschitz in the initial point uniformly in time, continuous in time, so
`continuousOn_prod_of_continuousOn_lipschitzOnWith'`), (iii) transport to `M` factored out of the (a)
proof (`chartField`, `isMIntegralCurveOn_extChartAt_symm_comp`) and identification with `integralFlow`
for `|t| < ε` by uniqueness on an open interval (`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`),
giving local joint continuity `exists_nhds_continuousOn_integralFlow`; (iv) compactness for one `ε₀`
(`exists_forall_continuous_integralFlow_of_abs_lt`), `integralFlow_nsmul` (iteration of the group law)
for continuity in the initial point at every time (`continuous_integralFlow_point`), and
`φ t x = φ (t − t₀) (φ t₀ x)` composed with the local statement at `(0, φ t₀ x₀)` for joint continuity.
Each `integralFlow hv t` is therefore a homeomorphism (inverse `integralFlow hv (−t)`, continuous), which
is the hypothesis shape `topFormMeasure_map_eq` takes; (b′) is now the only gap before (d′).

**Q29(b′) BUILT 2026-09-12 (L as priced, took L).** `Mathlib/Analysis/ODE/FlowDerivative.lean`, 7 pins, ★★
`ContDiffAt.exists_localFlow_form_invariant`: near any point, the local flow of a `C¹` field is differentiable in
the initial point for a uniform short forward time and pulls a `C¹` 2-form with vanishing flat Lie derivative
back to itself, `(ω (α x t)).compContinuousLinearMap (D(α · t) x) = ω x`. The Mathlib gap named above, smooth
dependence on initial data, is filled at the `C¹` level, which is all Liouville needs: (i) the variational
solution `Y' = Df(α x t) ∘ Y`, `Y 0 = 1` exists on a short interval by Picard–Lindelöf on the operator space
`E →L E` (`exists_linearODE_solution`; the time depends only on a bound for `‖Df‖` on the confinement set, so it is
uniform over the ball of initial points); (ii) ★★ `hasFDerivAt_flow_of_variational`: `α(x+h) − α(x)` is an
*approximate* solution of the linearised equation with defect `≤ ε L' ‖h‖` (mean value inequality on a small
ball, uniform continuity of `Df` on a compact thickening of the confinement set), `Y h` is an exact one, and
Grönwall (`dist_le_of_approx_trajectories_ODE_of_mem`, `gronwallBound_zero_le`) makes the gap `o(‖h‖)`;
(iii) `flatLieDeriv X ω z m = Dω(z)(X z)(m) + ∑ᵢ ω(z)(update m i (DX(z)(m i)))`, and along the curve the
product rule (`HasFDerivWithinAt.continuousAlternatingMap_apply`) gives `d/dt ω(α t)(Y t ∘ m) = (L_X ω)(α t)(Y t ∘ m)
= 0`, so `constant_of_has_deriv_right_zero` closes it. Forward time only (negative times come from the group law
downstream); `ProperSpace E` (finite dimensions in the application). One thing found on the way: `topFormMeasure_map_eq`'s
`hG` asks for `ContDiffAt ℝ ∞` of the chart expression of `g` but its proof uses only differentiability, so (d′)
needs it weakened to `DifferentiableAt` (an S edit), not `C^∞` dependence of the flow.

**Q29(c′) BUILT 2026-09-12 (M as priced, took M).** `Geometry/Manifold/HamiltonianLieDerivative.lean`, 10 pins. ★
`flatLieDeriv_eq_extDeriv_flatInteriorProduct_add` is Cartan's formula on a normed space, a `Fin 2`/`Fin 3`
computation from `extDeriv_apply` with the product rule `fderiv_continuousAlternatingMap_apply_apply` and the
antisymmetry of the form; ★★ `flatLieDeriv_localHamiltonianVector_localRep_eq_zero`: for a symplectic `α` and a
`C^∞` energy, the flat Lie derivative of `localRep α x₀` along `localHamiltonianVector α H x₀` vanishes at every
point of the chart's target, because `ι_X ω_loc = d(H ∘ chart⁻¹)` (the defining identity of the local vector, read
through `inverse_curryLeft_apply` / `apply_flatVec`) so its `extDeriv` is `d∘d = 0`, and `d ω_loc = 0` is closedness
through `localRep_mextDeriv`. `contDiffAt_localHamiltonianVector` was generalised from the chart image of `x₀` to
every point of the target (its proof never used the base point). (d′) is now assembly only.

**Q29(d′) BUILT 2026-09-12 (M as priced, took M). Q29 = G5 is CLOSED.** `Geometry/Manifold/HamiltonianFlowVolume.lean`
and `Instances/ProjectiveSpaceHamiltonianFlow.lean`, 12 pins. ★★★
`IsSymplectic.map_hamiltonianFlow_topFormMeasure_wedgePow`: on a compact symplectic manifold the Hamiltonian flow
`IsSymplectic.hamiltonianFlow hβ hH t` (= `integralFlow` of the Hamiltonian vector field) of every `C^∞` energy
preserves `topFormMeasure μ e (β^{∧k}) c` for every `k`, Haar `μ`, basis and chart cover, at every time; on `ℂℙⁿ`,
★★★ `Projectivization.fsVolume_map_hamiltonianFlow` and `fsVolumeNormalized_map_hamiltonianFlow`. The assembly, as
predicted: (i) `topFormMeasure_map_eq`'s `hG` weakened to `DifferentiableAt` (the S edit; `fsVolume_map_smul`
adjusted), and (b′)'s headline generalised to a two-sided ODE with a prescribed confinement set; (ii) the chart field
of (a′) is the trivialised section (`chartField_eq_trivializationAt_snd`, `rfl`), hence for the Hamiltonian field
it is `localHamiltonianVector` on the chart's target, so (c′) gives `hL`; (iii) ★
`exists_nhds_forall_integralFlow_localRep_eq`: in the chart the manifold flow IS the local flow for `|t| < ε`
(uniqueness on an open interval, exactly as in (a′)), so its chart expression is differentiable with derivative the
variational solution (`HasFDerivAt.congr_of_eventuallyEq` on the open ball) and pulls `localRep α` back to itself for
`t ∈ [0, ε/2]`; (iv) the wedge power is natural under pullback (`localRep_wedgePow`,
`wedgePow_compContinuousLinearMap`), a finite subcover gives one `ε₀`, and ★ the two-chart lemma
`forall_chart_of_forall_exists_chart` (the pullback identity in *some* chart around each point implies it for *every*
pair of charts, by `localRep_transition` across two transitions) produces `hG`/`hinv` in the exact shape
`topFormMeasure_map_eq` takes, with `integralFlowHomeomorph` (inverse: time `−t`); (v)
`map_integralFlow_eq_of_forall_Icc`: invariance for `t ∈ [0, ε₀]` gives all `t ≥ 0` by `integralFlow_nsmul` and
`Measure.map_map`, and `t < 0` by `φ t ∘ φ (−t) = id`. Nothing in the route needed a manifold Lie derivative or
manifold Cartan; the Mathlib gaps filled along the way are (a) global flows on compact manifolds, (a′) their joint
continuity, (b′) `C¹` dependence on initial data with the variational equation. `KahlerOnticSetup.flow_preserves_volume`
is now a theorem for **every** smooth Hamiltonian flow on `ℂℙⁿ`, not only the unitary ones; Posit 3 stands as written
(the constraint dynamics' measurement pieces are only locally Hamiltonian, `PiecewiseHamiltonian.lean`).

**Q29(e) BUILT 2026-09-12 (S–M as priced, took S).** The identification and the sector wiring, 8 pins. ★★
`Projectivization.hamiltonianFlow_schrodingerHamiltonian` / `hamiltonianFlow_torusHamiltonian`
(`Instances/ProjectiveSpaceSchrodingerFlow.lean`): the Hamiltonian flow of `−2⟨H⟩` IS `p ↦ exp(−itH) • p` and the
Hamiltonian flow of `2 ∑ θₖ μₖ` IS the torus orbit — `integralFlow_eq_of_isMIntegralCurve` on G4's/G16's integral-curve
theorems, with `schrodingerField_eq_hamiltonianVectorField` / `torusField_eq_hamiltonianVectorField` and
`schrodingerUnitary hH 0 = 1`. Hence ★★ `fsVolume_map_schrodingerUnitary_smul` (and the normalised one): Liouville for the
Schrödinger flow **from the Hamiltonian**, a corollary of `fsVolume_map_hamiltonianFlow`, proving the same equation as
`fsVolume_map_smul` by an independent argument. On the sectors (`LF4/SectorManifold.lean`):
`manyToOneSchrodingerSetup_flow_eq_hamiltonianFlow` (the sector's flow is the Hamiltonian flow on the base, the identity
on the fibre) and ★★★ `manyToOneSchrodingerSetup_flow_preserves_volume_derived` /
`unitaryFlowSetup_schrodingerUnitary_flow_preserves_volume_derived`: **the posited field `flow_preserves_volume` is a
theorem on the Schrödinger sectors by Liouville's theorem for the Hamiltonian flow**, the field not consumed in the proof
(the `_derived` discipline of `ManyToOneSchrodingerDerived.lean`). W1's "the preservation IS the invariance of that
volume" now has a second, Hamiltonian, derivation. Posit 3 unchanged, for the same reason as (d′).

### Q30 (= G17b): chart-independence of the Gram-density Riemannian volume — `S–M`

**What it would prove.** `MetricFamily.riemannianVolume` (`RiemannianVolume.lean`) does not
depend on the chart cover, for any metric family — today it is canonical on `ℂℙⁿ` only because it
is identified chart by chart with a top-form measure (`riemannianVolume_eq_smul_topFormMeasure`).

**Route.** The proof of `DifferentialForm.chartMeasure_congr` (`TopFormMeasure.lean`) verbatim, with
one lemma swapped: where the top-form proof uses `compContinuousLinearMap_apply_basis`
(`Alternating/TopForm.lean`: the coefficient of a pulled-back top form is `det` times the coefficient),
the Gram proof uses `√det (AᵀGA) = |det A| √det G`, which is `LinearMap.BilinForm.toMatrix_comp` +
`Matrix.det_mul` + `Matrix.det_transpose` + `Real.sqrt_mul_self` — all present, and the first three
were used in G17 (`det_toMatrix_fsModelMetric_mulVec`). Then `riemannianVolume_congr_cover` by the
proof of `topFormMeasure_congr_cover`. **Cx S–M, P high, value low** (no consumer; makes the generic
construction library-grade). The natural companion is `riemannianVolume_map_eq` (isometries preserve
the volume), the twin of `topFormMeasure_map_eq`, same price.

**Q30 BUILT 2026-09-11, as priced (S–M, took S).** One design point worth the record: the generic
`localRep` takes a bare family `g` (no bilinearity), so the Gram congruence `Aᵀ G A` is not even
statable for it; the theorems take `IsBilinear g` (a four-field Prop-structure, not a conjunction —
the conjunction form leaves `And.right`'s implicit `b` unconstrained when projecting the `smul`
clause). `localRep_transition` for metrics is `tangent_symmL_eq_fderiv` at both charts plus
`fderiv_chart_transition_comp`, finished with `congrArg₂` (the instance-path trap again: a `rw`
chain through `symmL` and `fderiv` will not close). On `ℂℙⁿ`, `isBilinear_fsMetric` needs the
scalar commutation `I • (c • a) = c • (I • a)` for `a` on the tangent-space instance path, which
`smul_smul` cannot see — prove it componentwise with `funext`. 14 pins.

### Q31 (= G18): Darboux — `XL`

**What it would prove.** Every symplectic form is locally the standard one. **Route** (Moser): a
local flow (Q29(a), locally — easier), the Poincaré lemma on a star-shaped set (**absent** at the pin:
`Mathlib/Geometry/Manifold/PoincareConjecture.lean` is the conjecture, not the lemma; nothing under
`DifferentialForm/`), and Moser's trick, which needs the flat Lie derivative and the ODE of Q29(b′).
So Q31 strictly contains Q29(b′) and adds the Poincaré lemma (M–L on a ball, by the explicit homotopy
operator). **Cx XL, P low–medium, value low** (nothing consumes it; it is the theorem a symplectic
library owes).

### R-016′: the arena-level `ι_X ω = dH` — `L`, statement-level — **LANDED 2026-09-14**

*(`LF4/ArenaSymplectic.lean` with `Instances/AddCircleTranslation.lean`, `ProductSelfModel.lean`,
`TranslationAtlasForm.lean`, `ProductForm.lean`. Items (1) and (2) of §3 are done — the arena is a
manifold over the product normed space with the product symplectic form, by a direct product-chart
construction rather than a general pullback — and (3)'s positive half, `IsLocallyHamiltonian` for
the stroke field, is proved; the non-exactness half is `BACKLOG.md` #28. Beyond the plan: Liouville
on the arena and the isolated Schrödinger dynamics as the arena's Hamiltonian flow. The paragraph
below is the pricing as it stood.)*


**What it would state.** That the record layer's joint-arena propagators (`RecordLayer/…`,
`H_int = g(t)(ι+1)δ·p_R`) are the time-`T` flows of Hamiltonian vector fields on the arena
`ℂℙⁿ × T² × …` for a product symplectic form. **What exists:** the manifold API on `ℂℙⁿ` (G1–G19),
`IsHamiltonianVectorField` for any real boundaryless manifold. **What is missing:** the arena as a
product *manifold* with a product symplectic form (product charted spaces and `IsManifold` for
products are present in Mathlib; a product `DifferentialForm` and its non-degeneracy is corpus work,
M), and the piecewise pieces stated on it. **Cx L, P medium, value medium** — it turns "Hamiltonian
generation stated, not formalised" (`TOUR.md`, `record-layer-plan.md`) into a stated theorem-shape;
a *discharge* is the `H_int` frontier (paper-side). Read `specs/frozen-base-obstruction-scoping.md`
first.

### Q32: glossary staleness sweep — `S`

11 entries flagged STALE by `check-glossary` (module moved since `reviewed:`), `bargmann` never
reviewed, `meta.sha` 147 commits behind. Re-read each against its module, correct, bump. Pure prose;
the guard lists the entries. **Value: site accuracy.**

### R-019: the relaxation H-theorem — `XL`, research

Blocked on first-passage asymptotics for the hyperbolic fibre; `relaxation_requires_hyperbolic_fibre`
(2026-09-06) is the proved precondition. Not a Mathlib gap, a mathematics gap. Highest value
*outside* the programme (new predictions). See `cr-queue.md` CR-14.

### Q33, built (2026-09-11) — A3 discharged

**What.** `Mathlib/Geometry/Manifold/Instances/AddCircle.lean` (Category 1): `Homeomorph.transportChartedSpace`
(the atlas `{ f.symm ≫ₕ e }`), `transport_transition` (the transported transitions ARE the source's, on the
nose: `f ≫ₕ f.symm` cancels by `Homeomorph.self_trans_symm` + `refl_toOpenPartialHomeomorph`), ★
`hasGroupoid_transport` / `isManifold_transport` (every groupoid transports), then `AddCircle.instChartedSpace`,
★ `AddCircle.instIsManifold` (`[Fact (T ≠ 0)]`, along `AddCircle.homeomorphCircle`) and ★ `instIsManifoldProd`
(the torus, Mathlib's product instance). Mathlib's `Instances/Quotient.lean` lists the quotient `IsManifold` as
its own TODO, so the transport is a genuine staging candidate. `LF4/ProjectiveManifold.lean`: `ktorus_isManifold`,
★★ `ksigma_isManifold` (the arena `ℂℙⁿ × T²`, over the REAL model of `ℂℙⁿ` — the one `fsForm` lives on — times
`(𝓡 1).prod (𝓡 1)`), ★★ `contMDiff_ksigma_fst`; `LF4/SectorManifold.lean`: ★★ `manyToOneSetup_pi_contMDiff`.
**S–M** as priced; took S. 11 pins.

**Two shelf facts.** (a) `Homeomorph.chartedSpace` (Mathlib's push-forward along `IsLocalHomeomorph.chartedSpace`)
has NO `IsManifold` companion and its atlas goes through `localInverseAt`, opaque to `rw`; building the transported
atlas directly as `f.symm ≫ₕ e` makes the transition identity a five-lemma `rw`. A class-valued `def` needs
`@[instance_reducible]`. (b) The W1 trap again: `(manyToOneSetup U p₀).pi` has domain `(…).Sigma`, opaque to
instance search — state on `KSigma (n+1)` with a `show`.

**What it does not do.** `homeomorphCircle` is not shown `C^ω` for the transported structure (identity in
charts; nothing consumes it). The arena's model is `𝓘(ℝ, Fin n → ℂ) × (𝓡 1 × 𝓡 1)`; a product *symplectic form*
on it is `R-016′`, for which this is now the prerequisite.

### The link-in audit (2026-09-11), for the record

Every G-series capstone traced to its consumers. Three physics sites should have cited the manifold
theorems and did not — `LF4/MomentMap.lean` (the object's own header), `LF4/ObservableFlow.lean`
(its conservation law is Noether for G16), `docs/TOUR.md` (no Hamiltonian row) — fixed in `d2063e5`.
Three capstones (`fsVolume_map_torusUnitary_smul`, `expectation_schrodingerUnitary_smul`, the
analytic twins) have no physics consumer and correctly none: corollaries whose content is carried
by their generic parents.

## References

[`BACKLOG.md`](BACKLOG.md) (list 3, and the `R-016` row of list 1);
[`../MATHLIB-GAPS.md`](../MATHLIB-GAPS.md) ("Kähler / symplectic manifold API");
[`TERMS.md`](TERMS.md) (Kähler, Hamiltonian, Liouville, moment map);
[`top-power-scoping.md`](top-power-scoping.md); [`exterior-derivative-scoping.md`](exterior-derivative-scoping.md);
[`frozen-base-obstruction-scoping.md`](frozen-base-obstruction-scoping.md); [`residues.tsv`](residues.tsv)
(`R-016`); `RecordLayer/PiecewiseHamiltonian.lean` (the flux correction);
`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`; `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`;
`Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`; [`future-work.md`](future-work.md).
