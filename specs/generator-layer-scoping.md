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
**The step-(4) ladder is complete except G5, which is queued at XL in §9 with the rest of the residue; G12 and G14a were built 2026-09-10.**
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
| **G5** | Liouville at manifold level: the time-`t` map of `X_H` preserves `topFormMeasure (ω^{∧n})` | **XL** | Low | Medium, and less than it looks | G3, and two absent Mathlib layers | ⛔ Needs global flows (absent) and `L_X ω = 0` by Cartan's formula (absent). It would replace the posit `ConstraintDynamics.flow_preserves` by a theorem — **for Hamiltonian flows only**, and the corpus's measurement pieces are *not* globally Hamiltonian (the flux correction), so it would not touch the dynamics the record layer actually uses. **Queued** — §9, re-priced there (the author's decision, 2026-09-10) |
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
| **G5** | **Liouville at manifold level**: the time-`t` map of `X_H` preserves `topFormMeasure (ω^{∧n})`. Three milestones. **(a)** the global flow of a `C^1` vector field on a compact manifold — global integral curves exist (`exists_isMIntegralCurve_of_isMIntegralCurveOn` at the pin gives them from a uniform local existence time; compactness supplies the uniform time), are unique (G4), and assemble into a `Flow` (`Mathlib/Dynamics/Flow.lean`); **(b)** the Lie derivative of a manifold form along the flow and Cartan's formula `L_X = d ∘ ι_X + ι_X ∘ d` — the genuine Mathlib gap (no `lieDeriv`, no Cartan at the pin; needs pullback of `DifferentialForm` along a smooth map and `mextDeriv` commuting with it); **(c)** `L_X ω = d(ι_X ω) = d(dH) = 0` (G11's `isLocallyHamiltonian` is exactly `d(ι_X ω) = 0`), so the flow preserves `ω`, hence `ω^{∧n}`, hence `topFormMeasure` (`topFormMeasure_map_eq`). | (a) **M–L**, (b) **L–XL**, (c) **M**; **XL** in all | Low–medium | Medium | Replaces `ConstraintDynamics.flow_preserves` by a theorem for the globally Hamiltonian pieces only; the measurement pieces are locally Hamiltonian (the flux correction), so Posit 3 stands even then. |
| **G14a** ✅ built 2026-09-10 | The Kähler predicate, atlas sense; `ℂℙⁿ` is Kähler | S–M (took **S**) | — | Medium | See §G14a above. |
| **G14b** | **Kähler in the tensor sense**: the Nijenhuis tensor `N_J` of a family `J` via `VectorField.mlieBracket` (at the pin), and `N_J = 0` for `IsKahler` — the easy direction of Newlander–Nirenberg (a holomorphic atlas makes `N_J` vanish, a chart computation: in a chart `J = J₀` is constant, and the bracket of coordinate-constant fields is `0`). The converse (`N_J = 0` ⇒ holomorphic atlas) is the hard PDE theorem and is **not** this row. | **M–L** | Medium | Low | Closes the `TERMS.md` "tensor sense" line; `IsKahler.nijenhuis_eq_zero`. Needs `J` as a section (G15) to state `[JX, JY]`. |
| **G15** | **`J` as a smooth section of `End(TM)`**: `fun x => (x, fsJ x)` is `C^∞` into the bundle of continuous linear maps `TangentSpace x →L[ℝ] TangentSpace x` (`Mathlib/Geometry/Manifold/VectorBundle/Hom.lean` at the pin); generically, `IsKahler` implies the section is `C^∞` because `J` is constant in every chart. | **S–M** | High | Low | The `TERMS.md` "smooth section" line; prerequisite of G14b. |
| **G16** | **The torus orbits are integral curves**: `t ↦ torusUnitary (t • θ) • p` is `IsMIntegralCurve` for `torusField θ`, and `momentMap` is conserved along it. | **S** | High | Low | The route of `isMIntegralCurve_schrodingerUnitary_smul` with `hasDerivAt_chartFun_torusUnitary` and `torusUnitary_add_smul`; the G4 write-up left it unwritten. |
| **G17** | **The Riemannian volume of the Fubini–Study metric is `fsVolume` up to the constant** (the `TERMS.md` Fubini–Study line "normalised Riemannian volume"). Needs the Riemannian volume measure of a metric on a manifold — absent at the pin (`VectorBundle/Riemannian.lean` has Riemannian *bundles*, no volume) — built as `topFormMeasure` of the volume form `√det g`; then `vol_g = ω^{∧n}/n!` is the algebraic Kähler identity from `g = ω (J ·, ·)` (G14a). | **L** | Low–medium | Low | Fills a Mathlib gap (Riemannian volume); nothing in the corpus consumes it. |
| **G18** | **Darboux's theorem** (the `TERMS.md` symplectic line): every symplectic form is locally the standard one. Moser's trick: needs G5(a) flows, G5(b) Cartan, and a Poincaré lemma on a ball. | **XL** | Low | Low | Nothing in the corpus consumes it; it is the classical theorem a symplectic library owes. |
| **W1** | **Wire the physics to the manifold layer**: the `ℂℙⁿ` instances of `KahlerOnticSetup` (`trivialKahlerOnticSetup`, `unitaryFlowSetup`, `manyToOneSetup`) get theorems that their `liouvilleMeasure` is `(4π)⁻ⁿ • fsVolume n` (the symplectic volume of `fsForm`, `fsVolume_eq_smul_fubiniStudyMeasure`), that `flow_preserves_volume` is `fsVolume_map_smul`, and that the sector carries `fsForm_isKahler`; and the four stale ledgers are corrected — link L1 of `specs/connectivity-manifest.md`, the `kahler_pointwise` docstring, and the `TERMS.md` Fubini–Study and symplectic entries, all of which still call the manifold residual open. The two projective-space types are definitionally equal (`ℙ ℂ (Ambient n)` is `CPN (n + 1)`). | **M** | High | **High** | This is what turns "we start from an FS, Kähler, Liouville space" into "the sector is the standard object, proved". Posit 3 is untouched by it. |
| **G19** | Analyticity of the Hamiltonian fields: `torusField`, `schrodingerField` are `ω` sections (the G3 route at `ω`; `hamiltonianVectorFieldSection` is `C^ω` for a `C^ω` form and energy). | **S–M** | High | Low | The G12 write-up left it unwritten. |

## References

[`BACKLOG.md`](BACKLOG.md) (list 3, and the `R-016` row of list 1);
[`../MATHLIB-GAPS.md`](../MATHLIB-GAPS.md) ("Kähler / symplectic manifold API");
[`TERMS.md`](TERMS.md) (Kähler, Hamiltonian, Liouville, moment map);
[`top-power-scoping.md`](top-power-scoping.md); [`exterior-derivative-scoping.md`](exterior-derivative-scoping.md);
[`frozen-base-obstruction-scoping.md`](frozen-base-obstruction-scoping.md); [`residues.tsv`](residues.tsv)
(`R-016`); `RecordLayer/PiecewiseHamiltonian.lean` (the flux correction);
`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`; `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`;
`Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`; [`future-work.md`](future-work.md).
