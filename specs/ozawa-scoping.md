# Ozawa error–disturbance: scoping note

**Status:** SCOPED 2026-09-04, not yet built. Expert-review row **B** of `specs/BACKLOG.md`
(M; likelihood *High* — "finite-dim, operator algebra only; a CSD twin follows the
`Uncertainty.lean` pattern"). Row B also gates **WAY brick 2** (row A), which has been waiting
behind it.

⚠️ **Read §2 before writing any Lean.** The row's one-line description hides the decision that
actually determines whether this is an M or an L: *which* inequality is the target.

## 1. What is being added, and why the corpus wants it

`Empirical/QM/Uncertainty.lean` has Robertson 1929 as pure inner-product geometry
(`robertson_uncertainty`: `Var_ψ(A)·Var_ψ(B) ≥ ¼‖⟪ψ,[A,B]ψ⟫‖²`), with the CSD volume-ratio
reading as its twin (`Empirical/CSD/Uncertainty.lean`, `csd_robertson_uncertainty`).

What is missing is the **measurement-theoretic** relation. Robertson bounds the *preparation*
spread of two observables in one state. It says nothing about a measurement's **error** or the
**disturbance** it inflicts — and the Heisenberg-microscope reading `ε(A)·η(B) ≥ ½|⟪[A,B]⟫|`,
which physicists quote and which experiment (Erhart et al. 2012, Rozema et al. 2012) has
**violated**, is not a theorem. Ozawa's universally valid relation is what replaces it:

  `ε(A)·η(B) + ε(A)·σ(B) + σ(A)·η(B) ≥ ½ |⟪ψ, [A,B] ψ⟫|`

with `σ` the standard deviations. The corpus asserting Robertson while staying silent about the
error–disturbance form is exactly the gap a post-2012 referee looks for.

## 2. ⚠️ The scoping decision: three different theorems wear this name

**(a) The naive Heisenberg form** `ε(A)·η(B) ≥ ½|⟪[A,B]⟫|` — **false**, and known false
experimentally. Not a target; the corpus should be able to say it is false, which needs a
counter-model, not a proof.

**(b) Ozawa's three-term relation** (Ozawa 2003) — the universally valid inequality above. This
is the row's stated target.

**(c) Branciard / Ozawa-tight forms** (Branciard 2013; Ozawa 2014) — stronger, tight in the
two-observable case, and considerably harder.

**Recommendation: (b) only, with (a) stated as what (b) replaces and NOT proved false in
Lean.** Exhibiting a violating model is a separate brick (it needs a concrete measurement model
whose `ε`, `η` are computed, not bounded), and conflating the two is how this row becomes an L.

## 3. What `ε` and `η` must be, and the definitional obligation

This is where the work is. Ozawa's `ε` and `η` are defined through a **measurement model**
`(K, σ, U, M)`: a probe space `K`, probe state `σ`, unitary `U` on `H ⊗ K`, and probe
observable `M`. Then, writing `A_in = A ⊗ 1`, `A_out = U† (1 ⊗ M) U`, `B_in = B ⊗ 1`,
`B_out = U† (B ⊗ 1) U`:

* **error** `ε(A)² = ⟪Ψ, (A_out − A_in)² Ψ⟫`
* **disturbance** `η(B)² = ⟪Ψ, (B_out − B_in)² Ψ⟫`

on `Ψ = ψ ⊗ σ`. So the brick needs a `MeasurementModel` structure. That is new vocabulary for
this corpus and is the part to get right before proving anything:

1. **Finite-dimensional, `Module.End ℂ H` with `IsSymmetric`** — follow `Uncertainty.lean`
   exactly, *not* the `Matrix` idiom, so the two files compose and the existing symmetric-operator
   API (`isSymmetric_sub_smul_one`, `expectation_conj`) is reused rather than duplicated.
2. **The tensor product — VERIFIED PRESENT 2026-09-04, the main risk is retired.**
   `QuantumInfo/JointRegister.lean`'s `tensorState`/`matrixLeft` are *matrix/coordinate* tools
   and are the wrong layer here. Mathlib's `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`
   supplies exactly what is needed, and it was probed rather than assumed: `TensorProduct.map A B`
   elaborates at `Module.End ℂ (H ⊗[ℂ] K)`, `TensorProduct.instInnerProductSpace` gives the inner
   product space, and `TensorProduct.inner_tmul` is the defining computation
   `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a,c⟫⟪b,d⟫`. Also available: `mapIsometry`, `congrIsometry`,
   `OrthonormalBasis.tensorProduct`. **So the `MeasurementModel` structure is three fields and a
   hypothesis**, with no bespoke tensor layer — and §6's stop condition is not triggered.
3. **`U` unitary as `LinearIsometryEquiv`** — the corpus's own idiom (see the memory note on
   `LinearIsometryEquiv`), not a bare `Module.End` with a conjugation hypothesis.

## 4. The proof, and why the row rates it *High*

Ozawa's proof is **operator Cauchy–Schwarz plus the triangle inequality**, on the same
centered-vector geometry Robertson already uses here. Concretely: write
`[A_in, B_in] = [A_out − A_in + A_in, …]`, expand the commutator into four terms, bound each by
Cauchy–Schwarz, and collect. `robertson_core` in `Uncertainty.lean` is the shape of the
Cauchy–Schwarz step and should be reused or generalised rather than re-proved (rule of two).

**No new analysis, no measure theory, no CSD ontology.** That is why the row rates likelihood
high, and why it belongs in `Empirical/QM/` as a Category-3 (promotion-ready) module.

## 5. The CSD twin — and what it must NOT claim

`Empirical/CSD/Uncertainty.lean` is the template: the QM file proves the inequality as pure
geometry; the CSD file states the **volume-ratio reading** under the observable correspondence
(LF4-todo §14), carrying the realisability obligation explicitly rather than asserting it.

⚠️ Three things the twin must not say, each a live failure mode in this corpus's prose:

* **Not** that CSD *explains* the error–disturbance trade-off. The inequality is a theorem of
  the Hilbert-space measurement model, which the record layer does not instantiate: the stroke is
  a skew product on the arena, not a linear isometry on `H_S ⊗ H_A` — the same reason WAY has no
  record-layer instance (`Empirical/QM/WignerArakiYanase.lean`, "Where this sits relative to CSD").
* **Not** that the corpus models an apparatus. Which physical `H_int` an apparatus realises is
  `RESIDUE(R-015)`, a modelling input. The probe `(K, σ, U, M)` here is an engineered witness.
* **Not** that Robertson is a special case of Ozawa. They bound different quantities;
  `σ(A)σ(B) ≥ ½|⟪[A,B]⟫|` appears *inside* Ozawa's relation as one of its terms, which is a
  different statement from implying it.

## 6. Deliverable, and the stop condition

`Empirical/QM/Ozawa.lean`:

* `MeasurementModel` (probe space, probe state, unitary, probe observable) with `error` and
  `disturbance`;
* ★★ `ozawa_error_disturbance` — the three-term relation;
* a **non-vacuity witness**: one concrete model where `ε ≠ 0` (a model with `ε = 0` everywhere
  would satisfy the inequality for uninteresting reasons — this is the `check-vacuity` lesson);
* the statement of the naive Heisenberg form as *what this replaces*, in prose, with the 2012
  experiments cited and **no Lean claim about its falsity**.

`Empirical/CSD/Ozawa.lean`: the volume-ratio twin, with §5's three disclaimers.

**Stop condition — declare and do not scaffold.** The tensor risk this was written for is
retired (§3.2, probed). It stands for what replaces it: if the three-term relation resists at the
Cauchy–Schwarz collection step, the honest outcome is to report the wall and stop, not to weaken
the statement into something provable. A two-term or `σ`-free variant would be a different (and
false) theorem.

## References

`specs/BACKLOG.md` row B (and row A, which waits on it); `Empirical/QM/Uncertainty.lean`
(`robertson_uncertainty`, `robertson_core`, the symmetric-operator API);
`Empirical/CSD/Uncertainty.lean` (the twin pattern and its LF4 §14 obligation);
`Empirical/QM/WignerArakiYanase.lean` (why the record layer instantiates neither WAY nor this);
`Mathlib/QuantumInfo/JointRegister.lean`; `specs/residues.tsv` (`R-015`);
`specs/future-work.md` (MT-1, the measurement-theoretic pillar row);
`specs/qm-empirical-tests.md` (the twins board). Sources: Ozawa 2003, *Phys. Rev. A* **67**,
042105; Erhart et al. 2012, *Nature Physics* **8**, 185; Rozema et al. 2012, *Phys. Rev. Lett.*
**109**, 100404; Branciard 2013, *PNAS* **110**, 6742.
