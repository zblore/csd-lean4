# Ozawa error–disturbance: scoping note

**Status:** SCOPED, `csd-foundations`-checked (15 findings folded), **BUILT and LANDED
2026-09-04**. Expert-review row **B** of `specs/BACKLOG.md`.

**As landed:** `Empirical/QM/Ozawa.lean` — `OzawaData`, `error`, `disturbance`,
★ `ozawa_commutator_identity`, ★★ `ozawa_error_disturbance`, the witness `zxWitness` with
★ `zxWitness_commutator_ne_zero` and ★ `ozawa_two_term_false`; `Empirical/CSD/Ozawa.lean` —
★ `no_ozawa_model_of_jointLift`. Six audit pins. `Uncertainty.lean` gained `stdDev` and the
unsquared ★ `commutator_le_two_mul_norm`, with `robertson_core` **re-derived from it** (§9.3, as
the plan required).

**One deviation from §3, recorded.** The plan had `MeasurementModel` as a probe space, three
fields and three hypotheses. Building it showed the tensor product plays **no part in the
inequality**: what the proof consumes is four symmetric operators on one space with the two "out"
operators commuting. So the theorem is stated at that level (`OzawaData`) and a measurement model
is one way to produce the data. This *strengthens* §3a's decision — there is now no tensor
vocabulary in the statement at all, so WAY brick 2 can share it whichever tensor it uses — and it
means `isSymmetric_map` and the normalisation hypotheses of §3 were **not needed**. They stay
recorded here as what a measurement-model instantiation will need; that instantiation is **not
built**.

This is a **breadth / hardening** row, not reconstruction-path work (`BACKLOG.md` "▶ NEXT STEPS",
item 4). It closes a coverage gap on the twins board; it does not advance the record layer (MD-1),
and §5 is what keeps the twin from reading as though it did. ⚠️ Row B is often described as gating
**WAY brick 2** — true (`way-theorem-scoping.md`), but brick 2 is rated **L** and is not queued,
so the gating argument is weaker than it sounds. The real case for B is §1's: the corpus asserts
Robertson and says nothing about the measurement-theoretic relation.

⚠️ **Read §2 and §3a before writing any Lean.** §2 is which of three theorems is the target; §3a is
a vocabulary decision that determines whether this row helps brick 2 or strands it.

## 1. What is being added, and why the corpus wants it

`Empirical/QM/Uncertainty.lean` has Robertson 1929 as pure inner-product geometry
(`robertson_uncertainty`: `Var_ψ(A)·Var_ψ(B) ≥ ¼‖⟪ψ,[A,B]ψ⟫‖²`).

What is missing is the **measurement-theoretic** relation. Robertson bounds the *preparation*
spread of two observables in one state. It says nothing about a measurement's **error** or the
**disturbance** it inflicts — and the Heisenberg-microscope reading `ε(A)·η(B) ≥ ½|⟪[A,B]⟫|`, which
physicists quote and which experiment (Erhart et al. 2012, Rozema et al. 2012) has measured
failing, is not a theorem. Ozawa's universally valid relation is what replaces it:

  `ε(A)·η(B) + ε(A)·σ(B) + σ(A)·η(B) ≥ ½ |⟪ψ, [A,B] ψ⟫|`

with `σ` the **standard deviations** (not variances) and `ψ` the **system** state. The corpus
asserting Robertson while staying silent on the error–disturbance form is exactly the gap a
post-2012 referee looks for.

## 2. ⚠️ The scoping decision: three different theorems wear this name

**(a) The naive Heisenberg form** `ε(A)·η(B) ≥ ½|⟪[A,B]⟫|` — **not universally valid**. It holds
under restrictive extra hypotheses (unbiased / independent-intervention measurements — Ozawa's own
qualification) and fails in general; Erhart 2012 and Rozema 2012 measured the failure. It is *not*
simply "false", and the corpus must not say that.

**(b) Ozawa's three-term relation** (Ozawa 2003) — the universally valid inequality above. The
target.

**(c) Branciard / Ozawa-tight forms** (Branciard 2013; Ozawa 2014) — strictly stronger, tight in
the two-observable case, considerably harder.

**Decision: (b) only.** (a) is stated in prose as what (b) replaces, with **no Lean claim about its
failure** — exhibiting a violating model needs `ε`, `η` *computed*, not bounded, and is a separate
brick. Conflating them is how row B becomes an L. (The §6 witness does refute the *two-term*
variant, which is a different and cheaper statement.)

## 3. What `ε` and `η` must be

Ozawa's `ε` and `η` are defined through a **measurement model** `(K, σ_probe, U, M)`: a probe space
`K`, probe state `σ_probe`, unitary `U` on the joint space, probe observable `M`. Writing
`A_in = A ⊗ 1`, `A_out = U† (1 ⊗ M) U`, `B_in = B ⊗ 1`, `B_out = U† (B ⊗ 1) U`, on `Ψ = ψ ⊗ σ_probe`:

* **error** `ε(A)² = ⟪Ψ, (A_out − A_in)² Ψ⟫`
* **disturbance** `η(B)² = ⟪Ψ, (B_out − B_in)² Ψ⟫`

**Hypotheses that are load-bearing and must be in the structure, not assumed silently:**
`‖σ_probe‖ = 1` (without it the centring that turns `‖(B_in − ⟨B⟩)Ψ‖` into `σ(B)` gives something
else), `M.IsSymmetric` (without it `ε²` is not real), and `‖ψ‖ = 1` on the theorem. So
`MeasurementModel` is a probe space, three fields and three hypotheses.

`stdDev` does not exist in the corpus — only `variance` (`Uncertainty.lean:53`). Add it *there*,
beside `variance`, with `variance = stdDev ^ 2`; do not define it locally in `Ozawa.lean`.

**Notation, pinned in the module docstring** (CONVENTIONS §9.2): `σ` is the standard deviation and
the probe state is `σ_probe`; `η` here is disturbance, and is **not** the measurement strength `η`
of `Empirical/CSD/WeakMeasurement.lean` in the same layer.

### 3a. ⚠️ The vocabulary decision — settle this before the first line

`Empirical/QM/WignerArakiYanase.lean` states its theorems over an **abstract** tensor
(`arakiYanase_identity`: `tensor : HS → HA → HT` with `h_tensor_inner` as a hypothesis), *not*
Mathlib's `⊗[ℂ]`. And `way-theorem-scoping.md` says brick 2 "shares every definition" with this
row (noise `N`, disturbance `D`). If `Ozawa.lean` is built on `H ⊗[ℂ] K`, brick 2 cannot share
those definitions without a conversion layer, and row B stops helping row A at all.

**Decision: state the core on the same `tensor` + `h_tensor_inner` interface WAY uses**, and give
the Mathlib `⊗[ℂ]` instantiation as a corollary. This keeps both bricks on one vocabulary and
makes §6's witness immediate through the kit that already exists (below).

**Mathlib support, verified by probe 2026-09-04 (pin `db584cd6d4`, v4.33.0), for the corollary
layer:** `TensorProduct.map A B` elaborates at `Module.End ℂ (H ⊗[ℂ] K)`;
`TensorProduct.instInnerProductSpace` (`Analysis/InnerProductSpace/TensorProduct.lean:144`);
`inner_tmul` (:69); `mapIsometry` (:217); `congrIsometry` (:268); `OrthonormalBasis.tensorProduct`
(:763). **One gap:** `IsSymmetric (TensorProduct.map A B)` from symmetric factors is *not* in
Mathlib — only `adjoint_map` (:704), `[FiniteDimensional]`-gated and in the `LinearMap.adjoint`
spelling CONVENTIONS §6 avoids. It is an ~8-line double `TensorProduct.induction_on`: list it as
the first lemma, `isSymmetric_map`.

**Rule of two (CONVENTIONS §9.3) — consume, do not rebuild.** `WignerArakiYanase.lean` is in the
same directory and already owns the concrete kit: `tensorEuc` / `inner_tensorEuc` (via
`Algorithms/HadamardTest.lean`), `ket` / `inner_ket` / `norm_ket`, `sigmaZ_ket`, `xPlus` / `xMinus`,
and CNOT as `LF5.vnUnitary 2` — and it `public import`s LF5, so `Empirical/QM/` may do the same.
`LF4.NaimarkDilation` (`LF4/POVMDilation.lean`) is probe-space-plus-isometry data and should be
checked before any new structure is written.

## 4. The proof: one algebraic identity, three Cauchy–Schwarz bounds

Write `N = A_out − A_in`, `D = B_out − B_in`. Expanding `[A_out, B_out] = [A_in + N, B_in + D]`
gives four summands, and **the left-hand side is zero**: `A_out = U†(1 ⊗ M)U` and
`B_out = U†(B ⊗ 1)U` are conjugates *by the same `U`* of `1 ⊗ M` and `B ⊗ 1`, which commute. Hence

  `[A_in, B_in] = −[A_in, D] − [N, B_in] − [N, D]`,

and the three terms are bounded by `2σ(A)η(B)`, `2ε(A)σ(B)`, `2ε(A)η(B)` — the first two after
centring `A_in`, `B_in`, which does not change the commutator (`commutator_shift`,
`Uncertainty.lean:71`).

⚠️ **`Commute A_out B_out` is a proof obligation, not a remark.** It is where the measurement model
enters and the only step of the argument that is not formal. A sketch that says "expand into four
terms and bound each by Cauchy–Schwarz" is wrong: the fourth term contains neither `ε` nor `η`, and
following it the proof cannot close.

**The Cauchy–Schwarz step, and a §9.3 obligation.** `robertson_core` (`Uncertainty.lean:87`) is the
right shape but is stated **squared** (`‖Aψ‖²·‖Bψ‖² ≥ ¼‖⟪ψ,[A,B]ψ⟫‖²`), so it cannot be applied
three times and summed across Ozawa's three *unsquared* products. §9.3 fires: extract the unsquared

  `commutator_le_two_mul_norm : ‖⟪ψ, (A*B − B*A) ψ⟫‖ ≤ 2 * (‖A ψ‖ * ‖B ψ‖)`

into `Uncertainty.lean` and **re-derive `robertson_core` from it** (the `momentMap_mk_of_norm_eq`
precedent), rather than proving a second Cauchy–Schwarz.

**No new analysis, no measure theory, no CSD ontology.** ⚠️ But the BACKLOG row's likelihood column
reads "High — operator inequality, **no new infrastructure**", and that half is inaccurate:
`isSymmetric_map`, the unsquared core, `stdDev` and the normalisation discipline are all new. The
**High** rating stands — it is mechanical — but the stated reason should not later be read as met.

## 5. The CSD twin — what it must be, and what it must not claim

⚠️ **Do not copy `Empirical/CSD/Uncertainty.lean` as a template.** That file is itself marked
**SCHEMA-MISMATCH** ("docstring claims CSD-side content the type does not carry") and
**TRANSPORT-ONLY**. Copying it silently adds a second such bundle, against the standing
no-placeholder rule. (It cites `PLACEHOLDERS.md` §7 for the *category*; §7's table lists only
`CSDCloningBundle` and `CSDUnitaryBundle`, so there is no row for it — do not cite one.)

⚠️ **There is no volume-ratio reading of `ε` and `η`.** LF4-todo §14's discharged correspondence
(`pauliDot_observable_correspondence`) matches the Hilbert expectation of a **system** observable
against a Σ-side integral. Ozawa's `ε`, `η` are expectations of **joint** operators in `ψ ⊗ σ_probe`:
there is no Σ-side fibre law for the probe factor and no ontic function for `A_out`.

**So the twin is a scope theorem, on the WAY brick 1 pattern**, not a transport bundle: the
record-layer stroke is **not** a `MeasurementModel` — there is no probe Hilbert factor, the stroke
is a skew product on the arena `ℂℙ^{N−1} × T² × ℂℙ^N` — so `ε` and `η` are not defined there at all.
That is an honest theorem and it sits beside `no_joint_hilbert_map`.

Three things the twin must not say:

* **Not** that CSD explains or predicts the error–disturbance trade-off. The inequality is a theorem
  about a Hilbert-space measurement model the record layer does not instantiate — the same reason
  WAY has no record-layer instance.
* **Not** that the corpus models an apparatus. Which physical `H_int` an apparatus realises is
  `RESIDUE(R-015)` (`residues.tsv`, boundary), a modelling input. The probe is an engineered witness.
* **Not** that Robertson is a special case of Ozawa. They bound different quantities and neither
  implies the other: Ozawa's three terms are `ε(A)η(B)`, `ε(A)σ(B)`, `σ(A)η(B)` — each pairing a
  *measurement* quantity with a *preparation* quantity — and the pure-preparation product
  `σ(A)σ(B)` appears in **none** of them.

## 6. Deliverable, and the stop condition

`Empirical/QM/Ozawa.lean`:

* `isSymmetric_map` (§3a's gap), then `MeasurementModel` with `error` and `disturbance`;
* ★★ `ozawa_error_disturbance` — the three-term relation, with `Commute A_out B_out` discharged;
* a **non-vacuity witness with nonzero right-hand side**. What trivialises this relation is
  `⟪ψ,[A,B]ψ⟫ = 0` (the bound reads `0 ≤ nonneg`) — **not** `ε = 0`, which is the sharpest and most
  interesting case: an exact measurement forcing disturbance. Corpus-native witness, using the kit
  in §3a: `A = M = σ_z`, `B = σ_x`, probe ground `|0⟩`, `U = LF5.vnUnitary 2` (CNOT), `ψ = |+y⟩`.
  Then `A_out − A_in` annihilates `Ψ`, so `ε(σ_z) = 0`; `B_out = σ_x ⊗ σ_x`, giving `η(σ_x) = √2`;
  `σ(σ_z) = 1`; RHS `= ½|⟪2iσ_y⟫| = 1`. The relation reads `0 + 0 + √2 ≥ 1` — non-vacuous,
  unsaturated, and it *is* the `ε = 0` case. Precedent: `way_hypotheses_satisfiable` in the sibling
  module (**not** `check-vacuity.sh`, which is about declarations nothing consumes);
* the naive Heisenberg form stated in prose as what this replaces, per §2(a).

`Empirical/CSD/Ozawa.lean`: the scope theorem of §5.

**Stop condition — declare and do not scaffold.** The risks are `Commute A_out B_out` and the
`IsSymmetric` transport across the tensor; if either resists, report the wall and stop. The
collection step will not resist (three applications of `commutator_le_two_mul_norm` and a triangle
inequality). Do **not** retreat to a two-term or `σ`-free variant: that is a different and false
statement, and the §6 witness refutes it outright (`εη + εσ(B) = 0 ≥ 1` is false there).

## References

`specs/BACKLOG.md` row B; `specs/way-theorem-scoping.md` (brick 2's shared definitions and the
sequencing — quantitative WAY is a corollary-level brick *after* B); `Empirical/QM/Uncertainty.lean`
(`robertson_uncertainty`, `robertson_core`, `commutator_shift`, `variance`, the symmetric-operator
API); `Empirical/QM/WignerArakiYanase.lean` (`arakiYanase_identity`'s abstract-tensor interface,
`way_hypotheses_satisfiable`, and the CNOT/`ket`/`xPlus` kit); `Empirical/CSD/Uncertainty.lean`
(⚠️ SCHEMA-MISMATCH / TRANSPORT-ONLY — not a template); `CsdLean4/LF4/POVMDilation.lean`
(`NaimarkDilation`); `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`; `specs/residues.tsv`
(`R-015`); `specs/future-work.md` (MT-1); `specs/qm-empirical-tests.md` (the twins board);
`PLACEHOLDERS.md` §7. Sources: Ozawa 2003, *Phys. Rev. A* **67**, 042105; Erhart et al. 2012,
*Nature Physics* **8**, 185; Rozema et al. 2012, *Phys. Rev. Lett.* **109**, 100404; Branciard 2013,
*PNAS* **110**, 6742.
