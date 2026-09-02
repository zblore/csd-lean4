# Generation from records — scoping the local-tomography brick (brick 2 of the Q11 arc)

**Status: SCOPED, `csd-foundations`-checked (18 findings folded), BUILT and LANDED 2026-09-02.**
Go/no-go given by the author 2026-09-02 ("yes do brick 2. scope first then execute"). Written against
HEAD `10f8738` for `specs/BACKLOG.md` "▶ NEXT STEPS 2026-09-02" item 2 (brick-2
generation-from-records, rated M–L), the composites residue of
[`unitary-tpp-scoping.md`](unitary-tpp-scoping.md) §3.1 and its §7 step 3. **§2 W3–W6 and §4 are
scope prose; the corpus claims are the theorem names of §3, all landed in
`SigmaLayer/TensorTomography.lean` and pinned in `Tests/AxiomAudit/SigmaLayer.lean`.**

⚠️ **This is not a "derive `⊗` from Σ" brick and must not be filed as one.** Local tomography is the
operational posit that, for complex local algebras (Paper C), singles out the tensor product among
merely-local composites; real-Hilbert-space QM is local and violates it, classical probability satisfies
it, so it follows neither from locality nor selects `ℂ`. Nothing below removes the posit. What the brick
does is the Q11 premise conversion (`unitary-tpp-scoping.md` §4): it replaces the *named-structure* form
of the posit ("the local algebras generate", `hgen` of `compositeAlgReconstruction`) by its *operational*
form stated in record vocabulary, proves the two equivalent, and shows the corpus's own composite sector
satisfies it. The surviving posit is registered as the permanent boundary **`R-017`**
(`residues.tsv`; carriers `TensorSolved.lean`, `TensorReconstruction.lean`, `TensorTomography.lean`).

**Placement (charter).** This is constraint work on the composite's observable algebra, **one level
above Σ** — [`CSD-CHARTER.md`](CSD-CHARTER.md)'s "constrain Σ from above" applied to composites: it pins
the composite *sector* (the epistemic projection of `Σ_AB`) given A6 locality + the record posit; nothing
is asserted about `Σ_AB` beyond its sector, and no ontic structure is touched. It is **not** record-layer
(MD-1) progress: no `{Ωᵢ(M)}` is context-fixed, no ontic
record is realised, and nothing here reads composite densities as `Ω₀`-ignorance (that reading is
Paper-side; LF1 has no density operators, and the brick uses `DensityOperatorIx` only as the corpus's
existing composite state type, the T9 vocabulary of `mixedEnsemble_capstone`).

## 1. What this scopes, in one line

`compositeAlgReconstruction` / `composite_dim_eq` (`SigmaLayer/TensorReconstruction.lean`) force the
tensor product and `k = m·n` from two premises on the local embeddings `ιA : M_m →ₐ 𝒜`, `ιB : M_n →ₐ 𝒜`:
they commute (`hc`) and they generate (`hgen : Algebra.adjoin ℂ (range ιA ∪ range ιB) = ⊤`). `hc` has a
Σ-referent (A6 composites: the two local observable algebras act on the composite sector and commute —
`aliceOp_bobOp_commute`, `leftOp_comm_rightOp`). `hgen` has none: it is a statement about a subalgebra
lattice, and the corpus's prose had been *calling* it local tomography (`TensorSolved.lean`,
`future-work.md` P3, `reconstruction-status.md` A6) without ever stating state-side local tomography as
a theorem. Brick 2 states it — **the joint record statistics of local contexts determine the
composite's epistemic state** (`RecordLocallyTomographic`) — and proves it equivalent to `hgen`, both
directions (`recordLocallyTomographic_iff_adjoin_eq_top`).

## 2. ★ Wall-check, done before any theorems

### W1 — Coverage both ways: three different things were called "local tomography"; none was the axiom.

Grep of `tomograph` across the corpus (2026-09-02, before the brick):

* `SigmaLayer/TensorGeneration.lean` `joint_mem_span_local` — every joint matrix on `Fin m × Fin n` lies
  in the span of `aliceOp U * bobOp Q`. This is the **operator-side** statement (the local products span
  the observable algebra) for the Kronecker sector only, and it legitimately carries the name: it is the
  *sufficiency* witness, not the state-side axiom. The brick's `kronecker_recordLocallyTomographic` is
  its record form.
* `CV/CompositeArena.lean` `arenaObs_join_mul`, docstring "★ Local tomography on the arena" — the
  expectation of `leftOp A * rightOp B` on a *join* `arenaJoin p q` factors into local expectations.
  ⚠️ **Mislabel.** That is the factorisation of product-state statistics, a property every composite
  (locally tomographic or not) has; local tomography is a statement about *arbitrary* joint states being
  fixed by product statistics. **Relabelled at landing** ("product expectations factor on joins", the
  docstring, the header bullet, and the `Extensions.lean` pin comment), cross-linked to
  `RecordLocallyTomographic`.
* `SigmaLayer/TensorSolved.lean`, `TensorReconstruction.lean`, `future-work.md` P3,
  `reconstruction-status.md` A6, `unitary-tpp-scoping.md` §3.2 — prose identifying the generation
  hypothesis with local tomography / local discriminability. Prose only. The identification is *true*
  (W3) but was never a theorem, which is exactly the §3.1 residue.
* `RecordLayer/JoinGeneration.lean`, `PointerGeneration.lean` — "generation" there is *Hamiltonian*
  generation of strokes (Schrödinger ODE), unrelated to algebra generation. Nothing to fold.
* `CV/CompositeArena.lean` `kronLeftHom` / `kronRightHom` (pre-brick names) — `A ↦ A ⊗ₖ 1`,
  `B ↦ 1 ⊗ₖ B` bundled as `AlgHom`s, over the `FieldConfig` index only; `composite_generate` proved
  `adjoin = ⊤` for the arena by the `matrix_eq_sum_single` + `single_eq_smul` + "each `single` is a
  product" pattern. The Kronecker sector on `Fin m × Fin n` needs the same two bundles and the same
  generation argument: **the rule of two (CONVENTIONS §9.3) fires** — Mathlib has
  `Matrix.kroneckerAlgEquiv` but no bundled factor embeddings, so they are staged as Cat-1
  `Mathlib/LinearAlgebra/Matrix/KroneckerAlgHom.lean` (`Matrix.kroneckerLeftAlgHom` /
  `kroneckerRightAlgHom` = `kroneckerAlgEquiv ∘ includeLeft / includeRight`, with the matrix-unit
  generation criterion `Subalgebra.eq_top_of_forall_single_mem`), and `CompositeArena` now consumes
  them (`leftHom` / `rightHom`; `composite_generate` through the criterion). This was the third
  rule-of-two count of the brick (the others: `outerProduct` index-generic with
  `IsHermitian.eq_eigen_outer` hoisted to any Hermitian matrix — `ChoiConverse`'s copy retired,
  `density_eq_eigen_ensemble` and `eq_eigen_ensemble` its corollaries; and
  `outerProduct_mul_outerProduct_trace`, the kernel of `born_quadratic`, which now consumes it).

Nothing in the corpus stated local tomography on the *state* side, for any composite. The dual form
(functionals) and the record form (density operators, local contexts) were both absent. Coverage the
other way: `compositeAlgReconstruction` had exactly one non-Kronecker consumer (`CV/CompositeArena.lean`
`compositeArenaForced`, whose `hgen` is discharged `Fin`-indexed on the arena by
`composite_generate_fin`); nothing consumed `composite_dim_eq` or `CompositeSector.ofReconstruction`
with a discharged `hgen` on `aliceOp` / `bobOp` over `Fin m × Fin n` — the non-vacuity of the
reconstruction's premises on the corpus's own composite sector was never exhibited there. Brick 2
supplies it (`kronecker_adjoin_eq_top`, `compositeAlgReconstructionOfRecords`).

### W2 — Infrastructure: everything needed is in Mathlib or the corpus; nothing was blocked.

Verified names (2026-09-02):

* `Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) : ∃ f, f ≠ 0 ∧ p ≤ ker f`
  (`Mathlib/LinearAlgebra/Basis/VectorSpace.lean`) — a proper subspace is killed by a nonzero functional.
  No finite-dimensionality needed.
* `Submodule.span_mul_span : span R S * span R T = span R (S * T)`; `Submodule.toSubalgebra` (a submodule
  containing `1` and closed under `*` is a subalgebra); `Algebra.toSubmodule_eq_top`;
  `Algebra.adjoin_le`, `Algebra.subset_adjoin`.
* `Matrix.matrix_eq_sum_single`, `Matrix.ext_iff_trace_mul_right` — the trace duality `f = tr(Y ·)`
  and "equal on all traces ⇒ equal". `Matrix.kroneckerAlgEquiv`, `Algebra.TensorProduct.includeLeft` /
  `includeRight`, `Matrix.stdBasis`, `Matrix.conjTranspose_kronecker`, `Matrix.mul_kronecker_mul`.
* `Matrix.IsHermitian.eigenvalues_eq_zero_iff`, `trace_eq_sum_eigenvalues` (its casts are
  `RCLike.ofReal`); `realPart_apply_coe`, `imaginaryPart_apply_coe`,
  `realPart_add_I_smul_imaginaryPart` (the Hermitian parts `ℜ X = (X + Xᴴ)/2`,
  `ℑ X = (X − Xᴴ)/(2i)`, `open scoped ComplexStarModule`).
* Corpus: `LF2.DensityOperatorIx ι` (Hermitian, PSD, trace one; index-parametric; `@[ext]` added),
  `LF2.DensityOperatorIx.traceForm ρ E = re tr(ρ.M E)` (the mixed Born rule, T9 capstone
  `mixedEnsemble_capstone`), `LF2.outerProduct` (index-generic after the brick),
  `LF2.IsHermitian.eq_eigen_outer` (any Hermitian matrix is the eigenvalue-weighted sum of its
  eigenvector projectors), `LF2.outerProduct_mul_outerProduct_trace`
  (`Tr(|ψ⟩⟨ψ| |φ⟩⟨φ|) = |⟨ψ,φ⟩|²`, the kernel of `born_quadratic`), `LF2.DensityOperatorIx.rankOne` +
  `traceForm_rankOne_outerProduct`, `LF2.trace_mul_isHermitian_real` (index-generic after the brick),
  `SigmaLayer.single_eq_smul`, `joint_mem_span_local`, `aliceOp_bobOp_commute`,
  `QuantumInfo.tensorState`, `RecordLayer.bornRateBasis` + `bornRateBasis_eq_inner_sq`.

### W3 — The CSD statement: a premise conversion with both directions, not a derivation.

The mathematical content, in order (theorem names as built):

1. **Products span the generated algebra.** For commuting `ιA`, `ιB`, the ℂ-span of the local products
   `localProducts ιA ιB = {ιA A * ιB B}` is closed under multiplication
   (`(ιA A ιB B)(ιA A' ιB B') = ιA(AA') ιB(BB')`, `mul_mem_localProducts`) and contains `1`
   (`one_mem_localProducts`), so it *is* a unital subalgebra (`localProductsSubalgebra`). Hence
   `hgen ⟺ span ℂ (localProducts ιA ιB) = ⊤` (`span_localProducts_eq_top_iff_adjoin_eq_top`).
2. **Dual form.** A subspace is `⊤` iff no nonzero functional kills it. So `span = ⊤ ⟺` *every linear
   functional on `𝒜` is determined by its values on local products* — **state-side local tomography,
   functional form** (`LocallyTomographic ιA ιB`; `locallyTomographic_iff_span_eq_top`, no commutation
   and no finite dimension needed; `locallyTomographic_iff_adjoin_eq_top` with `hc`).
3. **Record form** (`𝒜 = M_κ`). The corpus's epistemic states on the composite sector are the density
   operators `DensityOperatorIx κ`; a *local context* is a pair of local orthonormal bases `(bA, bB)`;
   the record rate of the joint outcome `(i, j)` is the mixed Born rate
   `productRecordRate ιA ιB ρ bA bB i j = traceForm ρ (ιA |bA i⟩⟨bA i| · ιB |bB j⟩⟨bB j|)`. **Record
   local tomography** (`RecordLocallyTomographic ιA ιB`): two density operators with the same record
   rates in every local context are equal. Theorem: `RecordLocallyTomographic ιA ιB ⟺ hgen`
   (`recordLocallyTomographic_iff_adjoin_eq_top`), given `hc` and that `ιA`, `ιB` preserve `star`
   (W4); also `recordLocallyTomographic_iff_locallyTomographic`.
   * `⇐` (`recordLocallyTomographic_of_span_eq_top`): the rank-one projectors of orthonormal bases
     span `M_m` (`span_onbProjectors_eq_top`: Hermitian decomposition `ℜ + iℑ` + spectral theorem
     `IsHermitian.eq_eigen_outer`), so `ρ = σ` is detected by trace pairings against the spanning set
     of product projectors (`eq_of_trace_mul_eqOn_span`, `span_localProducts_le_span_mul`). The
     reality of `tr(ρ P)` for Hermitian `P` (`trace_mul_isHermitian_real`,
     `traceForm_eq_iff_of_isHermitian`) is what lets the *real* record rates carry the complex trace —
     and the product projectors are Hermitian only because the embeddings preserve `star`
     (`isHermitian_apply_mul_apply`).
   * `⇒` (`span_eq_top_of_recordLocallyTomographic`): if the span is proper, a nonzero functional
     kills every local product, including `1`; it is a trace pairing `tr(Y ·)`
     (`exists_forall_eq_trace_mul`). Star-preservation makes the local products star-closed
     (`star_mem_localProducts`), so `Yᴴ` kills them too (`trace_conjTranspose_mul_eq_zero`), so one of
     the Hermitian parts is a nonzero Hermitian `H` killing them
     (`exists_isHermitian_ne_zero_of_trace_mul_eq_zero`); `tr H = 0` since `1` is a local product.
     Splitting the spectrum of `H` into positive and negative parts gives two *distinct density
     operators* `ρ`, `σ` (ensembles of `DensityOperatorIx.rankOne` over the eigenbasis) with
     `ρ.M − σ.M = c⁻¹ • H`, `c > 0` (`IsHermitian.exists_densityOperatorIx_sub_eq`), whose record rates
     agree in every local context. Contradiction.
4. **Consumers.** `compositeAlgReconstructionOfRecords` (`M_m ⊗ M_n ≃ₐ M_κ` from the record premise)
   and `composite_dim_eq_of_recordLocallyTomographic` (`k = m·n` from the record premise) — thin
   wrappers, docstrings say so. `CompositeSector.ofReconstruction` is *not* duplicated (§8.3b): the
   `iff` feeds its existing `hgen` argument. No functional-form wrappers were built for the same
   reason.
5. **Non-vacuity on the corpus's own sector.** `aliceOp` / `bobOp` bundled as `AlgHom`s
   (`aliceHom` / `bobHom` = `Matrix.kroneckerLeftAlgHom` / `kroneckerRightAlgHom`; `aliceHom_apply`,
   `bobHom_apply` are `rfl`), commuting (`commute_aliceHom_bobHom`), star-preserving (`aliceHom_star`,
   `bobHom_star`), generating (`kronecker_adjoin_eq_top`, from
   `adjoin_range_kroneckerLeftAlgHom_union_eq_top`) — hence `RecordLocallyTomographic aliceHom bobHom`
   is a **theorem** for the Kronecker sector (`kronecker_recordLocallyTomographic`,
   `kronecker_locallyTomographic`): the model satisfies the operational posit. That is the sufficiency
   half `joint_mem_span_local` restated in the record vocabulary, and the first discharge of
   `compositeAlgReconstruction`'s premises on `Fin m × Fin n`.
6. **Vocabulary bridge to the record layer** (`RecordLayer/StatisticsRigidity.lean`
   `productRecordRate_eq_bornRateBasis`): on the Kronecker composite, at a pure preparation
   `rankOne ψ`, the joint record rate of `(i, j)` IS `bornRateBasis b ψ l` — the basis-measurement Born
   rate of the joint register in any context `b` containing the product vector
   `tensorState (bA i) (bB j)` (`outerProduct_tensorState` + `traceForm_rankOne_outerProduct`). So the
   composites premise is stated in the *same* record vocabulary as `recordKernel`.

**What is and is not derived.** Items 1–3 are theorems with no physical input: they say the algebraic
premise and the record premise are *the same premise*. Item 5 says the corpus's composite sector
satisfies it. What is **not** derived — and cannot be — is that a composite sector *must* be locally
tomographic: that is the one operational axiom (Hardy's composites axiom `K = K_A K_B`, CDP's local
discriminability) that singles out `⊗` for complex local algebras, and `TensorSolved.lean` already says so. Brick 2 does not
change that sentence; it makes the posit *sayable in record vocabulary* and *checkable on the corpus's
sector*, which is what "generation from records" honestly means. The posit is `R-017`.

### W4 — The hypotheses, exactly: star-preservation is used both ways; states are density operators.

* **Star-preservation** (`hsA : ∀ A, ιA (star A) = star (ιA A)`, likewise `hsB`) enters **both**
  directions. `⇐`: the record rates are real parts of traces against the products `ιA(P) ιB(Q)`, and
  those are Hermitian only if the embeddings preserve `star`. `⇒`: the proof passes from a complex
  separating functional `tr(Y ·)` to a *Hermitian* one by taking Hermitian parts, and that step needs
  the killed set to be star-closed. The step is not cosmetic: for a general set of matrices the
  Hermitian-part trick fails — in `M_2`, the set `{E₁₁, E₂₂, E₁₂, i E₁₂}` is killed by
  `Y = c · E₁₂` (`tr(E₁₂ E₁₂) = 0`), but `Yᴴ = c̄ · E₂₁` is not (`tr(E₂₁ E₁₂) = 1`): the failing step
  is "`Yᴴ` also kills the set", and it fails exactly because the set is not star-closed. Whether the
  record-side equivalence survives for non-star algebra homs is not claimed either way. The brick takes
  star-preservation as a hypothesis — the physically mandatory one: local observables embed as
  observables. The Kronecker bundles satisfy it (`kroneckerLeftAlgHom_star`).
* **States.** The equivalence is with *density operators* as the states (the standard GPT formulation:
  Hardy, CDP — the state *space* is the convex set). The pure-state version ("two rays with the same
  local-context record rates are equal") is **not built**; under the same hypotheses it is
  *equivalent*, not weaker — the unital `*`-subalgebra structure of the local-product span makes any
  separating Hermitian `H` detectable already on pure preparations — but that converse is not a corpus
  theorem, and nothing here should be cited as if it were. In CSD the density operators are the corpus's
  existing composite state type (T9); nothing new is posited by using them.
* **Commutation** is needed for step 1 (span of products = generated algebra) and for the products to
  be Hermitian; it is the A6 locality the corpus already has.
* **Finite dimension** enters only through `𝒜 = M_κ` in the record form; the functional form is stated
  on any `ℂ`-algebra.

### W5 — Is local tomography derivable from Σ? **No — and the doc must say why, precisely.**

Σ supplies the composite sector as a projective sector with commuting local observable algebras (A6;
`RecordLayer/OnticComposite.lean` proves the ontic composite is not a product — `segre_range_isClosed`,
`exists_entangled_mem_nhds` — and `aliceOp_bobOp_commute` gives locality). Local tomography fails in
two independent ways, and `R-017` excludes both. (i) *The wrong field.* Over `ℝ` the Kronecker
construction *still generates* (the matrix-unit argument is field-agnostic), so the failure of real QM is
not a failure of generation of the full matrix algebra; it is that real QM's observables are the
*symmetric* matrices, and `dim Sym(mn) = mn(mn+1)/2 > [m(m+1)/2]·[n(n+1)/2] = dim(Sym(m) ⊗ Sym(n))`
(strict for `m, n ≥ 2`; the deficit `mn(m−1)(n−1)/4` is `dim(Antisym(m) ⊗ Antisym(n))`) — the local
products do not span the joint observable space. (ii) *Extra composite degrees of freedom beyond the
pair*, already over `ℂ` and inside the Lean's own type: `M_m ⊗ M_n ⊗ M_p` with `ιA = A ⊗ 1 ⊗ 1`,
`ιB = 1 ⊗ B ⊗ 1` is commuting, star-preserving and unital, and the third factor is invisible to every
local product, so `hgen` fails and `RecordLocallyTomographic` fails with it. Σ supplies neither the field
nor "the composite is exactly the pair". Conversely, local tomography alone does not select `ℂ`:
classical probability theory is locally tomographic. The brick's equivalence uses `ℜ`/`ℑ` and is a
fact about the *complex* composite. So the honest chain is: complex projective sectors (posit, Paper
C) ⇒ the Kronecker composite is locally tomographic (theorem, W3 item 5) ⇒ any composite sector
carrying the same local algebras and satisfying the record posit is the Kronecker one
(`compositeAlgReconstructionOfRecords`, theorem). The record posit is where the "why this composite"
question stops; the brick makes the stopping point a record statement instead of a lattice statement,
and `R-017` names it.

### W6 — Vocabulary check against the record layer.

`RecordLayer/BasisMeasurement.lean` states records for *pure* preparations as `bornRateBasis b ψ i =
‖⟨b i, ψ⟩‖²`; the mixed extension the corpus already uses is `LF2.DensityOperatorIx.traceForm` (T9,
`mixedEnsemble_capstone`: the mixed rate is the eigenvalue-weighted average of pure rates; `born_quadratic`
is the pure kernel). Brick 2's record rate is `traceForm` at the product of local rank-one projectors —
the same object, on the composite — and `productRecordRate_eq_bornRateBasis` (W3 item 6) makes the
identification a theorem rather than a reading. A *local context* is the pair of local orthonormal
bases; the joint outcome is the pair of local outcomes. No new record primitive is introduced. The Q11
template (`RecordLayer/StatisticsRigidity.lean`: `recordKernel` defined through `bornRateBasis`,
`RecordStatisticsPreserving ⟺ TransProbPreserving`) is the shape followed: define the operational
predicate through the record rate, prove the `iff` with the named-structure premise, re-premise the
consumers as labelled thin wrappers.

## 3. The brick (as landed)

### Placement and names

`SigmaLayer/TensorTomography.lean`, namespace `CSD.SigmaLayer`, importing `TensorReconstruction`,
`LF2/MixedEnsembleIx`, `LF2/EffectGleason`, `Mathlib/QuantumInfo/JointRegister`,
`Mathlib/LinearAlgebra/Matrix/KroneckerAlgHom`; pins in `Tests/AxiomAudit/SigmaLayer.lean` (the part
matching the namespace; 11 + 1), `Foundations.lean` (3 LF2 hoists) and `MathlibStaging.lean` (5 Cat-1
declarations). Library-grade (CONVENTIONS §9): API-first, every definition followed by its
characterising lemmas.

**Trace pairings** (`κ` any `Fintype`): `trace_conjTranspose_mul_eq_zero`,
`exists_isHermitian_ne_zero_of_trace_mul_eq_zero`, `eq_of_trace_mul_eqOn_span`,
`exists_forall_eq_trace_mul` (every functional on `M_κ` is `X ↦ Tr(Y X)`). The corpus already carried
two pure-state separation lemmas — `LF2.matrix_eq_zero_of_quadForm_zero` (`EffectGleason.lean`) and
`Empirical/CSD/PointerCommutation.lean` `exists_trace_mul_ne` (the contrapositive of Mathlib's
`Matrix.ext_iff_trace_mul_left`); the functional-form lemma sits beside them, and the consolidation is a
hardening-session item (BACKLOG item 3), not part of this brick.

**Orthonormal-basis projectors**: `onbProjectors ι`, `span_onbProjectors_eq_top`.

**Abstract half** (`𝒜` any `ℂ`-algebra, `ιA : M_m →ₐ[ℂ] 𝒜`, `ιB : M_n →ₐ[ℂ] 𝒜`):
`localProducts`, `one_mem_localProducts`, `apply_mem_localProducts_left` / `_right`,
`mul_mem_localProducts (hc)`, `star_mem_localProducts (hc) (hsA) (hsB)`, `localProductsSubalgebra (hc)`
(+ `localProductsSubalgebra_toSubmodule`), `span_localProducts_eq_top_iff_adjoin_eq_top (hc)`,
`LocallyTomographic`, `locallyTomographic_iff_span_eq_top` (no `hc`),
`locallyTomographic_iff_adjoin_eq_top (hc)`.

**Record half** (`𝒜 = M_κ`): `productRecordRate`, `RecordLocallyTomographic`,
`isHermitian_apply_mul_apply`, `traceForm_eq_iff_of_isHermitian`, `span_localProducts_le_span_mul`,
`recordLocallyTomographic_of_span_eq_top`, `IsHermitian.exists_densityOperatorIx_sub_eq`,
`span_eq_top_of_recordLocallyTomographic`, ★★ `recordLocallyTomographic_iff_adjoin_eq_top (hc) (hsA)
(hsB)`, `recordLocallyTomographic_iff_locallyTomographic`, `compositeAlgReconstructionOfRecords`,
★ `composite_dim_eq_of_recordLocallyTomographic`.

**Non-vacuity on the Kronecker sector:** `aliceHom`, `bobHom`, `aliceHom_apply`, `bobHom_apply`,
`aliceHom_star`, `bobHom_star`, `commute_aliceHom_bobHom`, `localProducts_aliceHom_bobHom`,
`kronecker_adjoin_eq_top`, `kronecker_recordLocallyTomographic`, `kronecker_locallyTomographic`;
`outerProduct_tensorState` (`|φ⊗ψ⟩⟨φ⊗ψ| = |φ⟩⟨φ| ⊗ₖ |ψ⟩⟨ψ|`).

**Record-layer bridge** (`RecordLayer/StatisticsRigidity.lean`): `productRecordRate_eq_bornRateBasis`.

**Upstream rule-of-two folds, same commit:** Cat-1 `Mathlib/LinearAlgebra/Matrix/KroneckerAlgHom.lean`
(`Submodule.eq_top_of_forall_single_mem`, `Subalgebra.eq_top_of_forall_single_mem`,
`Matrix.kroneckerLeftAlgHom` / `kroneckerRightAlgHom` + apply/mul/commute/conjTranspose/star lemmas,
`adjoin_range_kroneckerLeftAlgHom_union_eq_top`); `LF2/BornWrapper.lean` (`outerProduct` block
index-generic, `outerProduct_mul_outerProduct_trace`, `IsHermitian.eq_eigen_outer` hoisted;
`born_quadratic` consumes); `LF2/EffectGleason.lean` (`trace_mul_isHermitian_real` index-generic);
`LF2/ReducedDensity.lean` (`@[ext]` on `DensityOperatorIx`); `LF2/MixedEnsembleIx.lean`
(`DensityOperatorIx.rankOne`, `traceForm_rankOne_outerProduct`; the module-local `outerProduct` copy
retired; `eq_eigen_ensemble` a corollary); `LF2/ChoiConverse.lean` (its `eq_eigen_outer` copy retired);
`SigmaLayer/MixedEnsemble.lean` (`density_eq_eigen_ensemble` a corollary); `CV/CompositeArena.lean`
(`leftHom` / `rightHom` through the Cat-1 bundles, `composite_generate` through the criterion,
`arenaObs_join_mul` relabelled).

### What the Lean does not contain

No `sorry`, no `:= True`, no weakened stand-in for the `⇒` direction (the star/mixed-state route of W3
step 3 is the honest proof). No new `CompositeSector` constructor. No pure-state definition of the
predicate. No claim, in any docstring, that local tomography is derived from Σ. No dated parentheticals
or world-state status lexicon in Lean docstrings — the surviving posit is carried by the timeless
`⚠️ RESIDUE(R-017)` line in each carrier, with history in `residues.tsv` and git (CONVENTIONS §11).

### Docs at landing (done)

`specs/future-work.md` P3 row (record form landed, residual unchanged in substance, `R-017`);
`reconstruction-status.md` A6 row and residual bullet (the residual sentence carries the theorem name);
`BACKLOG.md` NEXT STEPS item 2 and row brick-2 (landed), hardening leftovers under item 3;
`unitary-tpp-scoping.md` §3.1 composites row and §7 step 3 (closed, name); `INDEX.md` row for this doc;
`residues.tsv` `R-017` (boundary; not mirrored in BACKLOG `## Residues`, which lists open rows only);
`TensorSolved.lean` / `TensorReconstruction.lean` headers (one paragraph each pointing at the record
form, tagged); `CV/CompositeArena.lean` `arenaObs_join_mul` relabel (W1) and its `Extensions.lean` pin
comment. No README/TOUR change (no headline claim changes); no `EMPIRICAL.md` row (not an empirical
twin).

## 4. ⚠️ What this must never be written as

* "Local tomography derived from records" / "the tensor product derived from Σ". It is a *premise
  conversion*: the posit survives, in record vocabulary (`R-017`). Real QM is the standing
  counterexample for `⊗`; classical probability is the standing counterexample for "local tomography
  selects `ℂ`".
* "Generation was already local tomography" as a *corpus theorem* before this brick. It was prose.
* "Product statistics factor" (`arenaObs_join_mul`) as local tomography. It is a property of product
  states, held by every local composite.
* "The pure-state version is strictly weaker". Under the brick's hypotheses it is equivalent; the
  converse is simply not built. Say "not built", not "weaker".
* A statement without star-preservation of the embeddings. Not what is proved (W4, both directions);
  the hypothesis is the physical one and is discharged on the Kronecker sector.
* Record-layer (MD-1) progress. It is constraint work one level above Σ (Placement paragraph).
* Any dated "(as of …)" or "still open" phrasing inside a Lean docstring for the surviving posit — the
  residue tag is the only sanctioned carrier of that status.

## 5. Sequencing (as executed)

1. This scoping doc → `csd-foundations` check (18 findings) → findings folded in place.
2. `SigmaLayer/TensorTomography.lean` built (abstract half, record half, Kronecker non-vacuity, the
   `StatisticsRigidity` bridge); the rule-of-two folds in the same commit, all consumers rebuilt.
3. Pins (20), docs (§3), guards after `git add`, commit, push, CI.
4. The BACKLOG order resumes: hardening session → LF / Ozawa twins → Q16 CP.

## 6. References

[`unitary-tpp-scoping.md`](unitary-tpp-scoping.md) (§3.1 composites row — the residue this closes; §3.2
local discriminability; §4 the conversion template; §7 step 3); [`future-work.md`](future-work.md) (P3,
SL-T3, B6); [`reconstruction-status.md`](reconstruction-status.md) (A6 "why ⊗" residual);
[`BACKLOG.md`](BACKLOG.md) (item 2, row brick-2); [`residues.tsv`](residues.tsv) (`R-017`);
[`CSD-CHARTER.md`](CSD-CHARTER.md) (constrain-from-above legitimacy: the record posit is a constraint on
the composite sector, one level above Σ, not a derivation of it). Lean surfaces:
`SigmaLayer/TensorTomography.lean` (the brick), `SigmaLayer/TensorReconstruction.lean`
(`compositeAlgReconstruction`, `composite_dim_eq`, `CompositeSector.ofReconstruction`),
`SigmaLayer/TensorGeneration.lean` (`single_eq_smul`, `joint_mem_span_local`),
`SigmaLayer/TensorSolved.lean` (`composite_is_tensor_product`), `SigmaLayer/TensorSector.lean`
(`aliceOp_bobOp_commute`), `RecordLayer/OnticComposite.lean` (A6 non-factorisation),
`LF2/BornWrapper.lean` (`outerProduct`, `IsHermitian.eq_eigen_outer`,
`outerProduct_mul_outerProduct_trace`, `born_quadratic`), `LF2/MixedEnsembleIx.lean`
(`DensityOperatorIx`, `traceForm`, `rankOne`, `ensemble`, `eq_eigen_ensemble`, `mixedEnsemble_capstone`),
`LF2/EffectGleason.lean` (`trace_mul_isHermitian_real`, `matrix_eq_zero_of_quadForm_zero`),
`Empirical/CSD/PointerCommutation.lean` (`exists_trace_mul_ne`), `RecordLayer/StatisticsRigidity.lean`
(the Q11 brick-1 template; `productRecordRate_eq_bornRateBasis`), `RecordLayer/BasisMeasurement.lean`
(`bornRateBasis`), `Mathlib/LinearAlgebra/Matrix/KroneckerAlgHom.lean` (Cat-1),
`CV/CompositeArena.lean` (`leftHom`, `composite_generate`, `arenaObs_join_mul`).

Neighbours (must-cite when this reaches the papers): L. Hardy, *Quantum theory from five reasonable
axioms*, arXiv:quant-ph/0101012 (2001) — the composites axiom `K = K_A K_B`; G. Chiribella, G. M. D'Ariano,
P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A **84**, 012311 (2011) — local
discriminability; W. K. Wootters, *Local accessibility of quantum states* (1990) and the real-QM
non-tomography example (the standing counterexample of W4/W5); the records-based Born derivation of
Axelsson (arXiv 2604.07418) for any "statistics-from-records" framing (`unitary-tpp-scoping.md` §6).
