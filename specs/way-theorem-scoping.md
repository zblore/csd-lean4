# The Wigner–Araki–Yanase theorem — scoping the conservation-law measurement brick

**Status: brick 0 LANDED (`Empirical/QM/WignerArakiYanase.lean`, 7 pins); brick 1 awaits the
author's placement decision (§3, "Landed" note); brick 2 deferred behind row B.** Written against
HEAD `8b99293` for `specs/BACKLOG.md` "Expert-review additions — 2026-09-02", row **A**; scoped
first, then built. Two theorems and one finding were scoped (§3); the finding (§2 W5–W6) is the part
that matters for the record layer and is the reason the spec preceded the Lean. **§2 W3–W7 and §4
are scope prose, not corpus claims; the corpus claims are the theorem names in §3 brick 0.**

⚠️ **This is not an `H_int` brick and must not be filed as one.** The `H_int(M)` arc is at its
paper-side end state (`frozen-base-obstruction-scoping.md`; `R-016`). WAY is a *measurement-theory*
theorem about conservation laws; it touches the record layer only through the question of §2 W5.

✅ **Anti-drift checked** (`csd-foundations`, 2026-09-02, per `CLAUDE.md`). The check returned
**DRIFT-RISK** against the first draft, and one finding was fatal to the draft's central sentence:
"everything the stroke conserves commutes with the context observable" is **false of the corpus's
own fibrewise witness** (`pointerEvolve` freezes the whole base, so it conserves every base
function, commuting or not). W3, W5 and brick 1 were rewritten around the correct — and sharper —
fact; §5 records what was withdrawn. Every corpus claim below was verified both ways.

---

## 1. What this scopes, in one line

Three things, in decreasing order of Lean content:

1. **The QM-side theorem** (Wigner 1952; Araki–Yanase 1960; Yanase 1961): a measurement
   interaction that conserves an *additive* quantity `L = L_S ⊗ 1 + 1 ⊗ L_A` can record an
   observable `A` of the system **exactly** only if `[A, L_S] = 0`. Absent from the corpus — every
   "Araki" hit is Araki–Lieb (entropy) and every "Wigner–Yanase" hit is skew information
   (`Mathlib/QuantumInfo/StrongSubadditivity.lean`, `lieb-dpi-scoping.md`). Finite-dimensional,
   four lines of inner-product algebra, QM-generic, promotion-ready like `no_cloning_two_state`.
2. **The CSD reading**, which is a *scope* statement and must be built as one: the constructed
   stroke is a skew-product map on the arena `ℂℙ^{N−1} × T² × ℂℙ^N`, not a linear isometry on a
   tensor product `HS ⊗ HA`, and no additive `L_S ⊗ 1 + 1 ⊗ L_A` is modelled — so **WAY's
   hypotheses have no instance at the record layer** (the LF5 `vnUnitary` tier *does* meet them,
   with an engineered `L`, and WAY's conclusion holds there trivially — brick 0's non-vacuity
   witness). Sharper still: the fibrewise witness freezes the
   base (`pointerEvolve_fst`), so it conserves *every* function of the base — the context rates
   (`IsJointLift.rate_conserved`) and equally the non-commuting `rotatedProj` expectation — while
   recording the context observable exactly on the shrunk cells. That combination is exactly what
   WAY forbids for tensor-product isometries; it is available here because the stroke is not one.
   One corollary at most, not a module (§2 W3).
3. **A finding, negative both ways** (§2 W5–W6): the record trilemma (`NullSeamWitness.lean`:
   seams / `ε`-Born / Dirac calibration) is **not** WAY in disguise, and the `ε` of `ε`-Born is
   **not** a WAY bound. The corpus's accuracy trade-off (`collapse_accuracy_bound`) is
   Landauer-shaped — accuracy bought with ready-state *measure* — while WAY's (Ozawa 2002) is
   bought with apparatus *variance* of the conserved quantity. Analogous conclusion, different
   mechanism, no theorem connecting them and none should be written.

---

## 2. ★ Wall-check, done before any theorems

### W1 — Coverage both ways: absent, and nothing to fold.

`grep -rn "Yanase\|WAY\|Wigner.Araki"` over `CsdLean4/`, `specs/`, `docs/` returns only the
skew-information mentions above. The conservation vocabulary that *does* exist is CSD-side and
states other things: `IsJointLift.rate_conserved` (the stroke's constants of motion),
`conserved_of_bracket_eq_zero` / `weight_conserved_of_disjoint` (`SigmaLayer/ChartBracket.lean`,
Poisson-commuting weights in a Darboux chart), `pointer_population_conserved` /
`pointer_basis_of_commuting` (`Empirical/CSD/PointerCommutation.lean`, `Einselection.lean` — the
einselection criterion `[P, H_int] = 0` ⇒ `P` conserved, and its characterisation
`pointer_invariant_iff_commute`). These are **neighbours, not the same theorem**: einselection is
about the pointer `P` and the interaction `H_int` on one space; WAY is about an *additive conserved
`L`* on a tensor product and the *exactly recorded* system observable. The WAY module should cite
`pointer_invariant_iff_commute` as the neighbour and re-prove nothing.

### W2 — Infrastructure: the abstract-tensor idiom suffices; the witness is a matrix computation.

The theorem needs, of the tensor structure, only the inner-product factorisation
`⟨tensor a b, tensor c d⟩ = ⟨a, c⟩ · ⟨b, d⟩` and the additivity of `L` on product vectors,
`L (tensor a b) = tensor (L_S a) b + tensor a (L_A b)`. The corpus already states no-go theorems
over an abstract `tensor : H → H → Htensor` with exactly this factorisation hypothesis
(`Empirical/QM/NoCloning.lean`, `NoDeleting.lean`, `NoBroadcasting.lean`); WAY generalises the
idiom to two *different* factors `HS`, `HA`. `U` enters only as an isometry commuting with `L`
(`∀ v, L (U v) = U (L v)`), so no `Matrix.exp`, no unitary group, no `Star` synthesis.

The non-vacuity witness lives at matrix level on `Fin 2 × Fin 2`, where the corpus already has the
measurement unitary: `LF5.vnUnitary 2` **is** CNOT (the adder permutation `(j,k) ↦ (j, j+k)`
mod 2; `vnUnitary_unitary`). The additive conserved quantity `L = Z ⊗ₖ 1 + 1 ⊗ₖ X` is a
`Matrix.kronecker` at the right type with no extraction needed; `Commute (vnUnitary 2) L` is a
`fin_cases`/`simp` computation. ⚠️ `tensorEuc` (`Empirical/QM/Algorithms/HadamardTest.lean`) is
*same-index* `κ × κ`; for the abstract theorem (two different factors `HS`, `HA`) that is the wrong
shape, but for the two-qubit witnesses both factors *are* `Fin 2`, so `tensorEuc`/`inner_tensorEuc`
are exactly right and were reused (this is what landed). If a witness with different factor
dimensions is ever needed, a two-index `EuclideanSpace ℂ κ → EuclideanSpace ℂ ι →
EuclideanSpace ℂ (κ × ι)` would be the rule-of-two extraction (CONVENTIONS §9); **do not extract
before then.**

### W3 — The CSD statement is a triviality and must be built as one.

What can be said in Lean about the CSD side is two lines (`jointLift_base` / `pointerEvolve_fst`
plus `rate_conserved`). Inflating it into a module or a capstone would violate CONVENTIONS §8.3b
(capstone discipline) and the placeholder rule. The honest shape is **one corollary in
`Empirical/CSD/`** (layer order; §3 Placement) — or prose only — whose docstring says what it is: *the
stroke is not a tensor-product isometry and models no additive conserved quantity, so the
theorem's hypotheses have no instance here; the fibrewise witness conserves every base function,
commuting or not, and records exactly — the combination WAY forbids where it applies*. Its value
is that a referee's "what about WAY?" gets a machine-checked pointer instead of prose. ⚠️ The
first draft's docstring — "the model conserves only torus-invariant quantities, which commute with
the context observable" — was **false** (§5) and must not reappear.

### W4 — WAY's hypotheses, exactly; the Yanase condition is not optional.

Araki–Yanase (finite-dim form). Data: Hilbert spaces `HS`, `HA`; an isometry `U` on `HS ⊗ HA`;
`L = L_S ⊗ 1 + 1 ⊗ L_A` with `L ∘ U = U ∘ L`; a unit apparatus-ready state `ξ`; system vectors
`a_i` (an orthonormal family — the eigenvectors of the measured `A`) with

  `U (a_i ⊗ ξ) = φ_i ⊗ ξ_i`,  `⟨ξ_i, ξ_j⟩ = 0` for `i ≠ j`   (distinct pointer readings: exact record).

Then for `i ≠ j`:

  `⟨a_i, L_S a_j⟩ = ⟨a_i ⊗ ξ, L (a_j ⊗ ξ)⟩` (the `L_A` term drops by `⟨a_i, a_j⟩ = 0`)
  `= ⟨U(a_i ⊗ ξ), L U(a_j ⊗ ξ)⟩` (conservation + isometry)
  `= ⟨φ_i, L_S φ_j⟩⟨ξ_i, ξ_j⟩ + ⟨φ_i, φ_j⟩⟨ξ_i, L_A ξ_j⟩ = 0 + ⟨φ_i, φ_j⟩⟨ξ_i, L_A ξ_j⟩`.

The first term vanishes by the exact record. **The second does not vanish by itself.** It vanishes
under EITHER of two extra hypotheses, and the theorem must be stated with one of them:

* **Yanase's condition** `⟨ξ_i, L_A ξ_j⟩ = 0` for `i ≠ j` — the pointer observable commutes with
  `L_A` (the apparatus's share of the conserved quantity is itself readable); or
* **repeatability** `⟨φ_i, φ_j⟩ = 0` — the post-measurement system states are orthogonal (the
  von Neumann–Lüders case `φ_i = a_i`).

With the `a_i` a basis and `A = Σ αᵢ |aᵢ⟩⟨aᵢ|`, `⟨a_i, L_S a_j⟩ = 0` off the diagonal gives
`Commute A L_S`. ⚠️ Dropping both extra hypotheses makes the statement **false**, and the
counter-model is one permutation matrix: **SWAP**, `U (a ⊗ ξ) = ξ ⊗ a`, conserves every symmetric
additive `L_S ⊗ 1 + 1 ⊗ L_S` — take total `σ_z` — and records `σ_x` **exactly** (`a_± = |±⟩`,
`ξ = |0⟩`, `ξ_± = |±⟩` orthogonal) although `[σ_x, σ_z] ≠ 0`: it is non-repeatable (`φ_± = |0⟩`)
*and* non-Yanase (`⟨+|σ_z|−⟩ ≠ 0`), so both escape terms are live. This is Ozawa's point (2002) that
the Yanase condition is load-bearing, and it belongs in brick 0 as the **second witness** — the
one showing the extra hypothesis is not decorative. The corpus's CNOT witness sits on the other
side: it conserves `Z ⊗ 1 + 1 ⊗ X`, its pointer `Z_A` does **not** commute with `L_A = X`, and it
is saved by repeatability. State both variants; never a third that drops both.

### W5 — Is the record trilemma WAY in disguise? **No.**

WAY costs exactness when a **linear isometry on `HS ⊗ HA`** conserves an additive `L` with
`[A, L_S] ≠ 0`. The stroke is not such an object. `pointerEvolve c ε (x, q) = (x, …)` is a skew
product on `ℂℙ^{N−1} × T² × ℂℙ^N` whose base is **frozen** (`pointerEvolve_fst`), so it conserves
*every* function of the base — the context rates (`rate_conserved`) and equally the expectation of
the non-commuting `rotatedProj` (`rotatedProj_not_commute`) — while recording the context
observable exactly on the shrunk cells (`born_lower`/`born_upper`). `jointLift c ε Δ` moves the
base only along its moment fibre by a diagonal-phase unitary (`jointLift_base`), conserving every
torus-invariant base function for every shift and every base function at `Δ = 0` (`jointLift_zero`).
**That combination — exact record of `A` plus conservation of a system quantity not commuting with
`A` — is precisely what WAY forbids for tensor-product isometries** (unconditionally: conserving
a system quantity itself is the `L_A = 0` case, where the Yanase side condition holds trivially),
and it is available here because no additive `L_S ⊗ 1 + 1 ⊗ L_A` and no linear joint dynamics is
modelled (W7). So WAY's hypotheses have no record-layer instance, and WAY cannot be the *source*
of any cost the trilemma records. ⚠️
The first draft argued this from "everything conserved commutes with the context" — false of the
fibrewise witness (§5); the conclusion stands on W7's reason, not on that one.

The trilemma's cost has a different origin, already theorems: connectedness
(`no_everywhere_correlation` — a continuous stroke cannot correlate a connected ready set with two
disjoint open pointer regions), openness (`posMeasure_noRecord_of_isOpenMap`,
`posMeasure_noRecord_pointer` — a positive-width ready region leaves a positive-measure no-record
set), and measure preservation (`collapse_accuracy_bound` — accuracy bought with ready-state
measure). None of these mentions a conserved quantity. The analogy "exact records are a limit" is
real; the mechanism is not shared. **A theorem connecting them would have to embed the CSD stroke
into the QM measurement model and then apply WAY to a conserved quantity the model does not have —
a construction with no consumer. Do not write it.**

### W6 — Quantitative WAY vs the `ε` of `ε`-Born. **Not the same `ε`.**

Ozawa's quantitative form (PRL **88**, 050402, 2002) bounds the measurement error from below by
`|⟨[A, L_S]⟩|²` over (a constant times) the apparatus variance of `L_A` (plus an output-side
variance term): exactness is approached only as the apparatus's spread in the conserved quantity
diverges. The `ε` in `pointerWeights c ε` is the **collar width of the smooth arc weights**
(`smoothArcWeight ε`, rates in `(2ε, 1)`) — a continuity parameter of the pointer profile, with
no conserved quantity behind it. The `ε`-Born horn's slack is the **collar measure of the smooth
arcs** (`born_lower`/`born_upper`, `volume ≥ rⱼ − 2ε`, `RecordLayer/PointerWeights.lean`); the
Dirac horn is priced by `collapse_accuracy_bound` (ready-state measure, `NullSeamWitness.lean`
"The corpus already prices Dirac calibration"). Neither is a variance in a conserved quantity.
**Finding, to be recorded in BACKLOG at landing: the two `ε`'s are unrelated; do not let a reader
identify them.**

Formalising Ozawa's bound needs the **noise-operator** formalism (`N = M_out − A ⊗ 1`,
`ε(A)² = ⟨N²⟩`) — which is precisely the infrastructure of the **Ozawa error–disturbance**
inequality (expert-review row **B**). So quantitative WAY is a *corollary-level* brick **after** B,
never before it, and never as its own infrastructure.

### W7 — The honest boundary: the record layer has no additive apparatus quantity.

"WAY has no instance here" means exactly: *the theorem's hypotheses are not met by the
record-layer stroke* (the LF5 `vnUnitary` coupling is a tensor-product isometry and meets them
with an engineered `L`; there WAY's conclusion holds and constrains nothing) —
the stroke is not a linear isometry on `HS ⊗ HA` and no additive conserved `L_S ⊗ 1 + 1 ⊗ L_A`
is modelled. It does **not** mean the CSD apparatus has been shown to carry its share of a
physical conserved quantity (energy, angular momentum) through a measurement that does not
commute with it, and it is **not** a compatibility result. The constructed stroke is a witness
with an engineered coupling (⚠️ RESIDUE(R-015)); no `L_A` on the pointer `ℂℙ^N`
(`Pointer N = CPN (N+1)`; the `T²` is the *system's* `KSigma` fibre) is modelled, so the
situation in which WAY *bites* — measure `σ_x` while total `J_z` is conserved — is outside what
the corpus constructs. If a future physical `H_int`
conserved such an `L`, WAY (and Ozawa's bound) would apply to it and the pointer would need
variance in `L_A`; that is a constraint on `R-015`'s domain, recorded here so it is not
rediscovered as a gap.

---

## 3. The bricks

### Brick 0 — the QM-side theorem (M; `Empirical/QM/WignerArakiYanase.lean`)

Category 3-Local, promotion-ready to 2-Framework exactly as `NoCloning.lean` is. Contents:

* **Statement, abstract tensor** — `arakiYanase_offDiag_eq_zero`: with the W4 data and *either*
  extra hypothesis (two theorems or one with the disjunction), `⟨a_i, L_S a_j⟩ = 0` for `i ≠ j`.
* ★★ **`wigner_araki_yanase`** — the ONB form: `Commute A L_S` for `A` diagonal in the `a_i`
  (equivalently `L_S` block-diagonal in `A`'s eigenspaces; in the finite-dim `Matrix` form via
  `Matrix.toEuclideanLin` or directly on `EuclideanSpace ℂ (Fin n)`).
* ★ **The no-go form**, which is the way the theorem is used: `¬ Commute A L_S → ¬ ∃ (U ξ ξ_i),
  exact Yanase-compliant (or repeatable) measurement of A conserving L`. Instantiate the contrast
  the corpus already owns: `rotatedProj` (the `qmH`-rotated projection,
  `Empirical/CSD/PointerCommutation.lean`; `qmH` in `Empirical/QM/Gates/SingleQubit.lean`).
  ⚠️ `rotatedProj_not_commute` is stated against `contrastH = diag(0, π)`, **not** against `Z`;
  since `qmZ = 1 − (2/π)·contrastH`, non-commutation transfers to `qmZ` by one linearity lemma
  (to be added in brick 0) ⇒ **no exact repeatable measurement of `σ_x` by any interaction
  conserving `σ_z ⊗ 1 + 1 ⊗ L_A`**.
* **Non-vacuity witness**: `LF5.vnUnitary 2` (CNOT) conserves `Z ⊗ₖ 1 + 1 ⊗ₖ X`
  (`cnot_commute_additive`), records `Z` exactly and repeatably (`vnUnitary` copies the system
  index), and the theorem's conclusion `Commute Z Z` holds — hypotheses satisfiable, and by the
  repeatability variant, since the pointer fails Yanase (W4).
* **Sharpness witness**: SWAP (`Equiv.prodComm` as a permutation matrix on `Fin 2 × Fin 2`)
  conserves `Z ⊗ₖ 1 + 1 ⊗ₖ Z`, records `σ_x` exactly, and `¬ Commute σ_x σ_z` — so the theorem
  **fails** once both extra hypotheses are dropped (`swap_exact_record_not_commute`). Without this
  the module would state a theorem whose side condition a reader could believe removable.
* **Cross-references in the docstring**: `pointer_basis_of_commuting` (converse direction),
  `csd_robertson_uncertainty` (the other uncertainty-type theorem), `no_cloning_two_state`
  (idiom), `specs/future-work.md`, this doc.
* **Pins**: `Tests/AxiomAudit/EmpiricalQM.lean`, ~6 (`propext, Classical.choice, Quot.sound`).
* **Twins board**: `qm-empirical-tests.md` §3.3b E1 → DONE with the theorem names.

Cost driver: the `Fin 2 × Fin 2` kronecker computations (`vnUnitary` is a permutation matrix
built from `Equiv.Perm`; `Matrix.kroneckerMap` on `Fin 2`); the abstract theorem itself is short.
**Do not** build a general measurement-model structure for this; the hypotheses are the structure.

**Landed** (`Empirical/QM/WignerArakiYanase.lean`, namespace `CSD.Empirical.QM.WignerArakiYanase`;
pins in `Tests/AxiomAudit/EmpiricalQM.lean`). Deviations from the list above, all deliberate:

* `arakiYanase_identity` is stated as a separate theorem (the master identity itself, with no side
  condition), and `arakiYanase_offDiag_eq_zero` takes the disjunction `Yanase ∨ repeatable` as one
  hypothesis rather than two theorems. `wigner_araki_yanase` asks its record hypotheses only
  *across distinct eigenvalues* `α i ≠ α j`, so a degenerate `A` is covered; the operators are
  `Module.End ℂ HS` and the conclusion is `Commute A L_S` via `Basis.ext` on `b.toBasis`.
* **The no-go instance is built on `sigmaX`/`sigmaZ` (`Contextuality/MerminPeres.lean`), not on
  `rotatedProj`**: importing `Empirical/CSD/PointerCommutation.lean` into an Empirical/QM module would
  invert the layer order (QM twins are QM-generic, "no CSD ontology"). `rotatedProj_not_commute` is
  cross-referenced in prose only, and the "one linearity lemma" `qmZ = 1 − (2/π)·contrastH` was not
  needed: `sigmaX_no_exact_conserving_record` runs `arakiYanase_offDiag_eq_zero` directly on the
  unnormalised eigenvectors `(1, 1)`, `(1, −1)` (`xPlus`, `xMinus`) with
  `⟨(1,1), σ_z (1,−1)⟩ = 2 ≠ 0`, concluding that *both* escape routes are closed (pointer violates
  Yanase **and** record is non-repeatable) for any `L_A`.
* **Non-vacuity is an existential, not a `Commute Z Z` capstone**: `way_hypotheses_satisfiable`
  exhibits `tensorEuc`, `chargeZX = σ_z ⊗ₖ 1 + 1 ⊗ₖ σ_x`, `L_A = σ_x`, CNOT (`vnUnitary 2`), `|0⟩`,
  `φ j = ξ' j = |j⟩` satisfying every hypothesis of `wigner_araki_yanase` **and** `⟨0|σ_x|1⟩ ≠ 0`
  (the pointer fails Yanase, so the repeatability disjunct carries the instance). Building blocks:
  `chargeZX_mul_cnot` (the `cnot_commute_additive` above), `chargeZX_cnot`, `chargeZX_tensorEuc`,
  `inner_cnot`, `cnot_record`, `cnot_pointer_not_yanase`.
* **Sharpness** `swap_exact_record_not_commute` is likewise existential: SWAP (`swapMap`, already in
  `HadamardTest.lean`, not a fresh `Equiv.prodComm` matrix), `chargeZZ`, ready state `|0⟩`, records
  `|0⟩ ⊗ (1, ±1)` — every hypothesis of `arakiYanase_offDiag_eq_zero` except `hside`, with
  `⟨a, σ_z a'⟩ = 2 ≠ 0` **and** both disjuncts of `hside` false.
* Rule of two, executed early: `Projectivization.inner_toEuclideanLin_unitary` was generalised in
  place to any finite index type (the isometry of CNOT on `Fin 2 × Fin 2`), closing `R-014`
  ahead of its consumer-count trigger because a stable-layer module may not import the Incubator
  prime. `inner_swapMap` was added beside `swapMap` (API-first, CONVENTIONS §9.1);
  `toEuclideanLin_kronecker_tensorEuc` lives in the WAY module to keep `Kronecker` out of the
  Hadamard-test import chain.
* The twins-board row is **ER1** in `qm-empirical-tests.md` (not "E1" as written above).

### Brick 1 — the CSD reading (S; placement open — see ⚠️ below)

⚠️ **Placement, found at brick 0's landing:** brick 1 cannot be a section of brick 0's module
after all. Its ingredients (`jointLift_base`, `pointerEvolve_fst`, `rotatedProj`) live in
`RecordLayer/` and `Empirical/CSD/`, and importing them into `Empirical/QM/WignerArakiYanase.lean`
would invert the layer order (QM twins are QM-generic by category). If built, it belongs in
`Empirical/CSD/` (a short section of `PointerCommutation.lean`, which already holds
`pointerEvolve`/`rotatedProj` material, or a small `Empirical/CSD/WignerArakiYanase.lean` twin
importing the QM module). The prose-only alternative is already in place: brick 0's docstring
carries the W5/W7 boundary in substance ("Where this sits relative to CSD").

* `jointLift_base_invariant_conserved` — for `f : LF4.CPN N → α` with
  `∀ g p, f (phaseUnitary g • p) = f p`, `f (jointLift c ε Δ y).1.1 = f y.1.1`
  (from `jointLift_base`). The moment coordinates are the instance (`rate_conserved`). Docstring:
  *torus-invariant base functions are conserved for every shift; for `Δ = 0` every base function
  is (`jointLift_zero`, `pointerEvolve_fst`)* — **never "only"**.
* `pointerEvolve_conserves_rotatedProj_expectation` (or the general `pointerEvolve_base_fixed`
  restated for an arbitrary `f`): the witness conserves a base quantity that does **not** commute
  with the context observable, while `born_lower`/`born_upper` record exactly on the shrunk cells.
  This is the machine-checked form of W5's point that the stroke sits outside WAY's hypotheses.
* Docstring records the W5/W7 finding verbatim-in-substance: *hypotheses have no instance; not a
  claim about physical conservation laws*.

⚠️ **Author decision**: brick 1 could equally be **prose only** in brick 0's docstring plus this
doc, with no theorem — the theorem is two lines and its only value is a machine-checked pointer.
Default now: **prose only**, per the Placement note above (the two lemmas are `rfl` consequences
of `pointerEvolve_fst` / `jointLift_base`, and a named `pointerEvolve_conserves_rotatedProj_…`
beside a WAY theorem is exactly the witness a reader would misread as "CSD evades WAY", §4); if
built, two lemmas in `Empirical/CSD/PointerCommutation.lean`, never a module.

### Brick 2 — quantitative WAY (L; **deferred behind row B**)

Ozawa 2002's bound on the noise-operator formalism. Shares every definition with the Ozawa
error–disturbance inequality (row B: noise `N`, disturbance `D`, the `ε(A)ε(B) + ε(A)σ(B) +
σ(A)ε(B) ≥ ½|⟨[A,B]⟩|` inequality). **Sequence: B first, then this as a corollary-level brick.**
Not started by this scoping; not queued until B lands.

---

## 4. ⚠️ What this must never be written as

* **"CSD derives / explains the WAY theorem."** WAY is a QM theorem about isometries on a tensor
  product; the CSD stroke sits *outside its hypotheses* (no tensor-product isometry, no additive
  `L`; W7) — not "consistent because it conserves only what it reads", which was withdrawn (§5).
  No derivation, no explanation — the theorem is stated on the QM side and the CSD side is a scope
  check.
* **"The trilemma is the WAY theorem."** W5. The trilemma's price is topological and
  measure-theoretic; WAY's is a conservation law. Do not let the shared conclusion ("exactness is
  a limit") suggest a shared mechanism.
* **"`ε`-Born is the WAY bound" / "the smooth pointer's `ε` is the apparatus variance."** W6.
* **"The CSD measurement conserves energy / angular momentum."** W7. It conserves the context's
  moment map and the register; no additive apparatus quantity is modelled (`R-015`). Compatibility
  with WAY is compatibility of the *model*, not a physical conservation claim.
* **A Lean statement of the form "WAY applied to the CSD stroke."** It would need a conserved
  quantity the model does not have; the correct output for that question is W7, in prose.

---

## 5. What was withdrawn from the first draft, and why

The first framing of row A said CSD is "WAY-compatible by construction" as if it were the result.
On inspection it is a *scope* fact (W3) with a boundary (W7): the model is compatible because it
contains no instance of the theorem's hypotheses, and that boundary is exactly `R-015`'s. The
result of this brick is the QM-side theorem plus the two negative findings (W5, W6); the CSD
reading is the smallest honest statement of the boundary, not a headline.

**Withdrawn after the `csd-foundations` check (2026-09-02).** The first draft's W3/W5 argued
"everything the stroke conserves commutes with the context observable, so WAY's premise `[A, L_S] ≠
0` never fires". False: the fibrewise witness `pointerEvolve` fixes the whole base
(`pointerEvolve_fst`, `rfl`), so every base function — including the `rotatedProj` expectation,
which does not commute (`rotatedProj_not_commute`) — is a constant of motion; `jointLift_zero`
makes this the `Δ = 0` member of the family brick 1 quantifies over, and a shift with equal phases
on two supporting coordinates does the same on that pair (`jointLift_base_moves_of_ne` needs the
phases to differ). The W5 conclusion survives on W7's reason (no tensor-product isometry, no
additive `L`), and the corrected fact is the sharper one: the ontic stroke realises exactly the
combination WAY forbids, which is possible only outside WAY's hypotheses. Also corrected in the
same pass: the `ε`-Born horn is priced by the collar measure, not by `collapse_accuracy_bound`
(which prices the Dirac horn); `rotatedProj_not_commute` is against `contrastH`, not `Z`; two file
attributions in §6.

---

## 6. References

Corpus: `specs/BACKLOG.md` (expert-review table, row A; NEXT STEPS item 1);
`specs/future-work.md` ("Pillar completeness", MT-1); `specs/qm-empirical-tests.md` §3.3b (ER1);
`specs/frozen-base-obstruction-scoping.md` (the arc this is *not* part of);
`specs/residues.tsv` (`R-015`, the boundary W7 sits on).
Theorems cross-linked: `IsJointLift.rate_conserved`, `isJointLift_jointLift`, `jointLift_base`,
`conservedData_torusAct` (`RecordLayer/JointLift.lean`); `momentContext`
(`RecordLayer/GlobalBasin.lean`); `pointerWeights` (`RecordLayer/PointerWeights.lean`);
`pointer_invariant_of_commute`, `rotatedProj_not_commute`,
`contrastH`, `pointer_basis_of_commuting`, `pointer_invariant_iff_commute`
(`Empirical/CSD/PointerCommutation.lean`); `qmH`, `qmZ` (`Empirical/QM/Gates/SingleQubit.lean`);
`pointerEvolve`, `pointerEvolve_fst` (`RecordLayer/PointerWeights.lean`); `smoothArcWeight`
(`RecordLayer/SmoothProfile.lean`);
`jointLift_zero`, `jointLift_base_moves_of_ne` (`RecordLayer/JointLift.lean`);
`IsJointLift.born_lower`, `IsJointLift.born_upper` (`RecordLayer/JointFlowTransfer.lean`);
`vnUnitary`, `vnUnitary_unitary`
(`LF5/VonNeumannUnitary.lean`); `no_cloning_two_state` (`Empirical/QM/NoCloning.lean`);
`inner_tensorEuc` (`Empirical/QM/Algorithms/HadamardTest.lean`); `csd_robertson_uncertainty`
(`Empirical/CSD/Uncertainty.lean`); `no_everywhere_correlation`, `collapse_accuracy_bound`
(`RecordLayer/MeasurementConstraints.lean`); `posMeasure_noRecord_of_isOpenMap`
(`RecordLayer/SharpenedNoGo.lean`); `posMeasure_noRecord_pointer`
(`RecordLayer/NoRecordGeometry.lean`); `poissonBracket_eq_zero_of_disjoint`,
`conserved_of_bracket_eq_zero` (`SigmaLayer/ChartBracket.lean`).

Literature: E. P. Wigner, *Z. Phys.* **133**, 101 (1952); H. Araki, M. M. Yanase, *Phys. Rev.*
**120**, 622 (1960); M. M. Yanase, *Phys. Rev.* **123**, 666 (1961); M. Ozawa, *Phys. Rev. Lett.*
**88**, 050402 (2002) (quantitative WAY); M. Ozawa, *Phys. Rev. A* **67**, 042105 (2003)
(error–disturbance, row B); L. Loveridge, P. Busch, *Eur. Phys. J. D* **62**, 297 (2011) (WAY for
position/momentum); M. Ahmadi, D. Jennings, T. Rudolph, *New J. Phys.* **15**, 013057 (2013)
(WAY as a resource-theoretic constraint).
