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
unchanged.** G2–G5, G7, G9–G13 not built. Every rating for step (4)
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
| **G2** | Existence and uniqueness of `X_H` pointwise: on a finite-dimensional tangent space `ω♭ x : v ↦ ω x (v, ·)` is injective by non-degeneracy, hence bijective, so `X_H x := (ω♭ x)⁻¹ (dH x)` | **M** | High | Medium | G1 | `TangentSpace 𝓘 x = E` by `rfl`; `LinearMap.injective_iff_surjective` on `E` and its dual. Pointwise only |
| **G3** | `X_H` is a smooth section of the tangent bundle | **M–L** | Medium–high | Medium (gates G4) | G2 | Inversion of `ω♭` along the bundle: `contDiffAt_ring_inverse` on the units plus the `localRep` chart plumbing that `ExteriorDerivative.lean` already does for forms. This is the `VectorBundle/Hom.lean` pattern again |
| **G4** | Integral curves of `X_H` exist and are unique, and `H` is conserved along them (`ι_X ω (X) = 0` by alternation) | **S–M** | High | Medium | G3 | Direct application of Mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt` and `isMIntegralCurve_eq_of_contMDiff`; lifts `conserved_along_translationCurve` from the chart to the manifold |
| **G5** | Liouville at manifold level: the time-`t` map of `X_H` preserves `topFormMeasure (ω^{∧n})` | **XL** | Low | Medium, and less than it looks | G3, and two absent Mathlib layers | ⛔ Needs global flows (absent) and `L_X ω = 0` by Cartan's formula (absent). It would replace the posit `ConstraintDynamics.flow_preserves` by a theorem — **for Hamiltonian flows only**, and the corpus's measurement pieces are *not* globally Hamiltonian (the flux correction), so it would not touch the dynamics the record layer actually uses. **Not scheduled** |
| **G6** | The moment map of the torus action on ℂℙⁿ at manifold level: the fundamental vector field `X_A` of `p ↦ exp(tA)·p` (the `t`-derivative of `uTrans`, which `contDiffOn_uTrans` already makes smooth), `μ_A [z] = ⟨z, iA z⟩/‖z‖²`, and ★★★ `IsHamiltonianVectorField fsForm X_A μ_A`; for `A = diag(iθ)` this is `LF4.momentMap` | **L** | Medium | **High** | G1 only (the field is given, G2/G3 are not needed) | Closes the `TERMS.md` moment-map line "NOT established: that it is the moment map of a Hamiltonian torus action on the symplectic *manifold*". It is also exactly the route the 2026-08-02 review recorded for the Hamiltonian-origin row: unitary rotations on a compact Kähler pointer are globally Hamiltonian (`H¹(ℂℙ^K) = 0`). The computation is `fsModelForm_apply` (M7) against the derivative of the action in the chart; half of it exists |
| **G7** | A manifold-level Kähler predicate `IsKahler ω J g` on ℂℙⁿ: `J = i·` on each tangent space (chart-independent because the transitions are ℂ-analytic, `contDiffOn_uTrans`), `g = ω(·, J·)`, the pointwise triple `IsFubiniStudyKahler` lifted | **M** | High | Low–medium | — | Packages words the corpus already has pointwise; closes the last non-analyticity item of the `TERMS.md` Kähler line. Gates nothing |

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
G5, not scheduled. `R-016′` **L**, medium, value medium, and it is a statement, not a discharge.
Nothing here has been "attempted and walled"; every absence above was a grep.

## 8. Additions after G1 and G6 (2026-09-08, late): G8–G13

The remaining "not established" lines of `TERMS.md` and `POSITS.md`, each as a numbered brick. Every
shelf claim was grep-probed at the pin on 2026-09-08. These IDs supersede the chat-only labels used
earlier the same evening.

| # | Brick | Cx | P(success) | Value | What it lands, honestly |
|---|---|---|---|---|---|
| **G8** | **A moment map is unique up to a constant, and the normalisation pins it.** (A) On `ℂℙⁿ`, two `MDifferentiable` Hamiltonians `H, K` of the same field for the same 2-form family differ by a constant. (B) If `Hₖ` is a Hamiltonian for the `k`-th phase field `torusField (Pi.single k 1)`, `Hₖ ≥ 0`, and `∑ₖ Hₖ = 2` (the form's scale), then `Hₖ = torusHamiltonian (Pi.single k 1) = 2 · momentMap · k`. | **M** | High | **High** (ledgers) | The sentence `POSITS.md` bullet 1 calls "the standard symplectic argument, unformalised" becomes a theorem, given G6. **Posit 1 is unchanged**: it asserts that the *dynamics* generates the torus action; G8 only says the map that action has is the corpus's. Appends to `Instances/ProjectiveSpaceMomentMap.lean` (no new file). |
| **G9** | The image of `momentMap` is exactly the standard simplex | S–M | High | Medium | `momentMap_sum_eq_one` and `momentMap_nonneg` give `⊆`; `⊇` by exhibiting `mk (fun k => √tₖ)`. Closes the "moment polytope" line for this action, without the convexity theorem. |
| **G10** | The torus flow preserves the Fubini–Study volume: `Measure.map (torusUnitary θ • ·) (fsVolume n) = fsVolume n` | S | High | Medium | A one-line corollary of `fsVolume_map_smul`. Liouville in the dynamics sense for the flow G6 built, without G5. |
| **G11** | Hamiltonian implies locally Hamiltonian | M | High | Low–medium | `mextDeriv` of a 0-form family is `mfderiv` (flat half upstream: `extDeriv_constOfIsEmpty`) plus smoothness of the 0-form section and `d ∘ d = 0`. |
| **G12** | `fsForm` is analytic, not merely `C^∞` | M–L | Medium | Low | Real-analyticity of `log(1 + ‖z‖²)`; registry line only. |
| **G13** | The `U(n+1)` moment map `⟨z, iAz⟩/‖z‖²` for a general skew-Hermitian `A` | M–L | Medium | Low–medium | The G6 computation with a non-diagonal velocity; the corpus uses the torus. |

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

## References

[`BACKLOG.md`](BACKLOG.md) (list 3, and the `R-016` row of list 1);
[`../MATHLIB-GAPS.md`](../MATHLIB-GAPS.md) ("Kähler / symplectic manifold API");
[`TERMS.md`](TERMS.md) (Kähler, Hamiltonian, Liouville, moment map);
[`top-power-scoping.md`](top-power-scoping.md); [`exterior-derivative-scoping.md`](exterior-derivative-scoping.md);
[`frozen-base-obstruction-scoping.md`](frozen-base-obstruction-scoping.md); [`residues.tsv`](residues.tsv)
(`R-016`); `RecordLayer/PiecewiseHamiltonian.lean` (the flux correction);
`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`; `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`;
`Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`; [`future-work.md`](future-work.md).
