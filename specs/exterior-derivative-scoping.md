# The exterior derivative on manifolds (step 2b): scoping note

**Status:** SCOPED 2026-09-07; §3.1 attempted the same day. **NOT BUILT.** ⚠️ §3a records two
retracted findings from that attempt and the procedural lesson behind them — read it before
trusting any "wall" claim in this note. Step (2b) of the manifold exterior-calculus
plan ([`BACKLOG.md`](BACKLOG.md) XL, [`MATHLIB-GAPS.md`](../MATHLIB-GAPS.md)).

⚠️ **Read §2 before writing any Lean.** There are three standard routes to `d` on a manifold,
they differ by more than taste, and a probe at the pin settles which one to take — one of the
other two is blocked on machinery Mathlib does not have.

⚠️ **This is the wall, and it is upstream's own.** The flat-forms file names manifolds in its
`## TODO`. Steps (0), (1) and (2a) each turned out cheaper than their rating; **do not
generalise from that to this one.** The three of them together were an afternoon; this is the
item the row has always priced at XL, and nothing found while scoping it argues otherwise.

---

## 1. What is being added

After step (2a), a differential form on a manifold is an object:
`DifferentialForm I M n ι G`, a `C^n` section of `x ↦ TₓM [⋀^ι]→L[𝕜] G`. What it does not
have is a **derivative**. Until `d` exists:

* `dω = 0` at manifold level is not statable, so the Kähler closedness the corpus proves flat
  (`Kahler.extDeriv_fundamentalFormAlt`) stays flat;
* the top-power identity `ω^(N-1)/(N-1)! = μ_FS` is sayable (steps (0)+(1)) but has no route
  to a proof, because everything downstream of it is integration of `dω`-shaped objects;
* `R-016` — the arena-level `ι_X ω = dH` — has no manifold-level `d` to be stated against.

⚠️ **None of that means the corpus is blocked on it.** It is not: `μ_FS` is pinned by
uniqueness-under-symmetry, the moment-map equation is proved at the linear level, and
`R-016`'s residue is recorded as open mathematics either way. This is self-containment.

## 2. ⚠️ Three routes, and the probe that picks one

**Route A — chart-local, glued by naturality.** Define `dω` at `x` by pushing `ω` into the
chart at `x`, applying the flat `extDeriv`, and pulling back; prove chart-independence.

✅ **Take this one.** Its crux — that the flat exterior derivative commutes with pullback — is
**already proved upstream**: `extDeriv_pullback` in
`Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`,

    extDeriv (fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)) x
      = (extDeriv ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)

for `ContDiffAt 𝕜 r f x` with `minSmoothness 𝕜 2 ≤ r`. Chart transitions are exactly such
maps, so well-definedness is an application of a lemma that exists rather than a theorem to
prove. `extDeriv_extDeriv` then transports `d² = 0` the same way.

**Route B — the invariant (Palais) formula.** Define `dω(X₀,…,X_k)` by the alternating sum of
derivatives along vector fields plus the Lie-bracket correction.

⚠️ **Not as the definition.** The ingredients exist — manifold Lie brackets
(`Geometry/Manifold/VectorField/LieBracket.lean`) and tensoriality tooling
(`Geometry/Manifold/VectorBundle/Tensoriality.lean`) — but making this a *definition* requires
proving the right-hand side is tensorial, i.e. depends on the vector fields only through their
values at the point. That is the classical hard step and it is not in Mathlib. **It is the
right thing to prove *afterwards*** (§5): the flat version already exists as
`extDeriv_apply_vectorField`, so the manifold statement has a template and a target.

**Route C — antisymmetrised covariant derivative.** Define `d` from a torsion-free connection.

⛔ **Blocked, and the probe is unambiguous.** Mathlib has `CovariantDerivative` and `torsion`
(`Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic,Torsion}.lean`), but it has **no
existence theorem for a connection, no Levi-Civita construction, and no torsion-free
existence** — searched at the pin, zero hits. Route C would first have to build existence by
partitions of unity, then prove `d` independent of the choice. That is strictly more work than
Route A and it buys nothing Route A does not give.

## 3. Route A, concretely, in build order

1. **The local representative.** For `ω : DifferentialForm I M n (Fin k) G` and a chart at `x`,
   its expression as an unbundled flat form `EM → EM [⋀^Fin k]→L[𝕜] G`. This is where the work
   is: it composes the chart with the tangent-bundle trivialisation, and the tooling is
   `ContinuousLinearMap.inCoordinates` plus `tangentBundleCore`'s trivialisations — the same
   machinery `mfderiv` uses for functions, applied to sections.
2. **`mextDeriv`** — flat `extDeriv` of the local representative, pulled back to `x`.
3. **Chart-independence**, by `extDeriv_pullback` on the transition map. If step 1 is set up
   well this should be short; if it is fighting, step 1 is wrong, not this.
4. **Smoothness**: `mextDeriv ω` is a `C^(n-1)` section — i.e. the result really is a
   `DifferentialForm`, which is what makes `d` iterable.
5. **`mextDeriv_mextDeriv`** — `d² = 0`, transported from `extDeriv_extDeriv`.

## 3a. ⚠️ §3.1 attempted 2026-09-07 — the first write-up was WRONG, twice

**Read this section as a correction, not as a finding.**

`localRep` was written and **typechecks**. The base-point identity —
`localRep form x₀ (extChartAt I x₀ x₀) = form x₀` — was then attempted as the smallest test.

⚠️ **First write-up (retracted): "Mathlib has every construction in that chain and none of the
computation lemmas."** That is false. The lemmas exist and the file's own docstring points
straight at the main one:

* `FiberBundle.trivializationAt_continuousAlternatingMap_apply` — the alternating bundle's
  trivialisation in terms of `inCoordinates`, and it is **`rfl`**;
* `ContinuousAlternatingMap.inCoordinates` + `inCoordinates_eq` — the same through continuous
  linear equivalences;
* `VectorBundleCore.trivializationAt_symmL` — `@[simp, mfld_simps]`, the trivialisation's
  `symmL` as a `coordChange`;
* `VectorBundleCore.coordChange_self` — and that coordinate change is the identity at the
  base point.

⚠️ **Second write-up (also retracted): "the next brick is a trivialisation-unfolding API,
rated M–L."** There is no such brick to build. With the four lemmas above the base-point
identity reduces — checked — to exactly one goal:

    (form x₀) (⇑((trivializationAt EM (TangentSpace I) x₀).symmL 𝕜 x₀) ∘ v) = (form x₀) v

which is `trivializationAt_symmL` + `coordChange_self`, and what stops `rw` closing it is that
`TangentSpace I` and `(tangentBundleCore I M).Fiber` are **defeq but not syntactically equal**
— a `show`/`change`, not a theorem.

**Corrected finding: there is no level below §3.** The route-A plan stands as written, and the
work is the ordinary chart-plumbing it always was: `extChartAt` round-trips that must be
rewritten *before* the trivialisation is unfolded (rewriting after, the `extChartAt` is already
delta-reduced and the rewrite will not fire), and `TangentSpace`-vs-`Fiber` bridging at each
`VectorBundleCore` lemma. Neither is deep; both are constant friction, and **that friction is
what the XL is made of** — not any single missing theorem.

### ⚠️ The procedural lesson, which is the real output of this attempt

Four "walls" were recorded on 2026-09-07 and **all four were wrong**: an instance-path
mismatch that was an ascription, a missing hypothesis that was a missing `IsManifold`, and the
two retracted above. Every one was called after a failed `simp` or a failed `exact`, and every
one dissolved on the next probe. The corrective is procedural and cheap:

* **before recording a wall, follow the file's own docstrings** — this one names
  `FiberBundle.trivializationAt_continuousAlternatingMap_apply` in a comment eleven lines above
  the definition that needed it, and it was not read;
* **a failed tactic is evidence about the tactic, not about Mathlib.** Grep for the lemma by
  name before concluding it does not exist;
* **the cheapest disproof first.** "Are these the same instance?" was one `rfl`; "does this
  lemma exist?" was one `grep`. Both were skipped in favour of a paragraph.

## 4. ⚠️ Four traps, all of them design decisions rather than difficulties

* **Degree indexing.** `DifferentialForm` (step 2a) is indexed by an arbitrary `ι`, but
  `extDeriv` goes `Fin k → Fin (k+1)`. `d` therefore exists only for `ι = Fin k`. **Decide
  early** whether to specialise the type, add a `Fin`-indexed abbreviation, or carry an
  equivalence — and do not discover this halfway through step 3.
* **Smoothness arithmetic.** `d` of a `C^n` form is `C^(n-1)`. Stating that in `WithTop ℕ∞`
  arithmetic is bookkeeping that will leak into every downstream statement. ⚠️ **Consider
  stating the whole file at `n = ω` or `∞` first**, where `n - 1 = n`, and generalising later
  only if a consumer needs it. This is the single decision most likely to double the work if
  taken the other way.
* **`minSmoothness 𝕜 2 ≤ r`.** The pullback lemma needs it; over `ℝ` it is `2`, over other
  fields it can be `ω`. Carry it as a hypothesis rather than assuming `ℝ`.
* **`UniqueDiffOn`.** The `Within` versions need it. Chart images are open, so it holds — but
  it has to be *supplied*, and the `extDerivWithin`/`extDeriv` split will show up in the proofs.

## 5. What to prove once `d` exists

In rough order of value:

* `mextDeriv_mextDeriv` (`d² = 0`) — the reason the object is worth having;
* linearity, and `d` of a `0`-form is the differential;
* ★ the **Palais formula** as a theorem (Route B's content, now a consequence rather than a
  definition), mirroring `extDeriv_apply_vectorField`;
* naturality: `d(f*ω) = f*(dω)` for `C^∞` maps of manifolds — the manifold analogue of the
  lemma the construction is built on;
* ⚠️ **the Leibniz rule `d(α ∧ β) = dα ∧ β + (-1)^{|α|} α ∧ dβ`** — needs the wedge of
  *sections*, which is a fibrewise application of `ContinuousAlternatingMap.wedge` (step (1))
  and is **not built**. Scope it separately; it is not free.

## 6. Deliverable and stop condition

**Deliverable:** `Mathlib/Geometry/Manifold/ExteriorDerivative.lean` — `mextDeriv`,
chart-independence, smoothness, `d² = 0`, and a non-vacuity witness on `ℂℙⁿ` (the corpus's own
manifold since step (0)).

**⛔ Stop condition.** If the local representative (§3.1) does not come out in a form that makes
§3.3 short, **stop and re-scope rather than pushing through**. A `d` whose chart-independence
proof is a fight is a `d` defined the wrong way, and the resulting definition will be unusable
downstream even if it typechecks. Landing a half-usable `d` would be worse than landing none:
every later statement would inherit it.

## 7. Rating

**XL**, and the row has always said so. P(success) medium *for Route A specifically*, because
the crux lemma exists; low for anything that goes near Routes B or C first.

⚠️ **A caution the session that scoped this earned the hard way.** Three ratings were corrected
on 2026-09-07 — step (2) M–L when it was L, then L when its blocking lemma turned out to exist,
then two "walls" that were a missing hypothesis and a type ascription. In every case the error
came from **pricing by what is present rather than by what is missing**. For this item that
cuts the other way: the presence of `extDeriv_pullback`, Lie brackets and covariant derivatives
makes the shelf look full, and the shelf is not the work. **Re-price after §3.1 is written**,
which is the first point at which anyone knows anything.

## References

* `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` — flat `extDeriv`,
  ★ `extDeriv_pullback` (the crux), `extDeriv_extDeriv`, and the `## TODO` naming manifolds.
* `Mathlib/Analysis/Calculus/DifferentialForm/VectorField.lean` — `extDeriv_apply_vectorField`,
  the flat Palais formula (§5's target, §2's rejected definition).
* `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` — manifold Lie brackets.
* `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic,Torsion}.lean` — Route C's
  ingredients, and the absence of an existence theorem that blocks it.
* `Mathlib/Geometry/Manifold/VectorBundle/Tensoriality.lean` — what Route B would need.
* `CsdLean4/Mathlib/Geometry/Manifold/DifferentialForm.lean` — the type `d` acts on (step 2a).
* `CsdLean4/Mathlib/Analysis/Normed/Module/Alternating/Wedge.lean` — the wedge §5's Leibniz
  rule would need at section level.
