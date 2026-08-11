# C1 formal support map

Which C1 claims the repository actually supports, by exact module, theorem,
scope, assumptions and axiom result. Created 2026-08-10.

**No prose-only assurances.** Every row names a constant that exists at the
recorded commit, or says explicitly that no theorem establishes the claim.

⚠️ **On citation.** Cite the **repository** at a tagged release, by commit SHA,
module path and theorem name. Do **not** cite "LF5" or "LF6" as documents: those
manuscript layers are unpublished, and citing them would be a dependency-order
violation. The repository is one artefact with its own DOI, so citing it at a
tag is not.

## Axiom posture

Every constant below reports exactly `[propext, Classical.choice, Quot.sound]`
— the foundational triple, nothing else. Pins live in
`CsdLean4/Tests/AxiomAudit/{Foundations,EmpiricalQM,Dynamics,LF4}.lean`, matched
by `#guard_msgs`, so drift breaks the build.

Checked specifically (C1 work-order item 24): the Born-volume chain behind the
pointer-volume results is clean, and stronger than clean —
`EffectGleason` is **not in the 53-module transitive import closure** of
`LF6/LocalDeisolationFlow.lean`. The route never reaches Busch at all, so its
absence is a fact about the dependency graph rather than about axiom bookkeeping.

## The map

| C1 claim | Theorem | Module | Scope and assumptions |
|---|---|---|---|
| Bell-local CHSH bound | `lhvCHSH_abs_le_two` | `Empirical/QM/Crypto/E91.lean` (ns `CSD.Empirical.QM.E91`) | Any shared probability space; measurable `±1` responses. No CSD content. |
| Singlet violates it | `chsh_singlet_at_optimal_angles` | `Empirical/QM/Bell.lean` | Canonical CHSH quadruple. |
| Forced contextuality | `no_product_partition_realises_singlet` | `LF6/ForcedContextuality.lean` | Quantifies over **any** `(Λ, μ)`; setting-local `±1` product responses. Reproduction required at **every** setting pair. |
| — its non-vacuity | `productPartition_nonvacuous` | same | Makes the no-go a separation. |
| **C1 four-answer obstruction** | `no_compatible_global_chsh_assignment_realises_singlet` | `LF6/C1BellConsistency.lean` | **One shared state space.** Reproduction required only at the **four CHSH settings**, so strictly weaker in hypothesis than the row above and not subsumed by it. Measurability assumed **only** of the posited `S`; the global assignment's four responses are *derived* measurable. |
| — its non-vacuity | `compatibleGlobalCHSH_nonvacuous` | same | Separation, not artefact. |
| No-signalling, kernel level | `singlet_operational_no_signalling` | `LF3/OperationalNoSignalling.lean` | Kernel identity, both wings. Assembled from `context_no_signalling_a/b`. |
| — marginals are ½ | `singlet_marginals_eq_half` | same | Every context. |
| Local de-isolation coupling | `localDeisolation_factorises` | `LF6/LocalDeisolationFlow.lean` | `V_loc = V_A ⊗ V_B`, by construction. Finite dilated construction only. |
| **Nudge locality** | `localNudge`, `localNudge_born` | `LF6/NudgeLocality.lean` | Locality is **definitional**: `localNudge := (U_A(a) ⊗ U_B(b))ᴴ ψ⁻` for the proved-unitary `wingBasisUnitary`. No `hgen`. |
| — wing unitary | `wingBasisUnitary_mem_unitaryGroup` | `LF3/Spinor.lean` | Via projector completeness. |
| **Full chain locality** | `localMeasurementChain_factorises` | `LF6/NudgeLocality.lean` | `(V_A ⊗ V_B)(U_A ⊗ U_B)ᴴ = (V_A U_Aᴴ) ⊗ (V_B U_Bᴴ)`. **Dynamical** locality of the finite dilated construction. |
| Pointer reproduction, generic | `localDeisolation_pointer_volume` | `LF6/LocalDeisolationFlow.lean` | ⚠️ Carries `hgen`, so **excludes `a·b = ±1`**. |
| Pointer reproduction, **all settings** | `localDeisolation_pointer_volume_local` | `LF6/NudgeLocality.lean` | **No `hgen`.** Covers perfect (anti)correlation. |
| No-signalling of the construction | `localDeisolation_no_signalling_A` / `_B` | `LF6/NudgeLocality.lean` | Equality of **marginal volumes**, not of outcome partitions. Under measurement independence. |

## What is NOT established

**Bell-local outcome factorisation is not recovered, and cannot be.**
`no_product_partition_realises_singlet` forbids it. Nothing in the locality
results above weakens this: they are dynamical locality of the finite
construction, not factorisation of outcomes.

**The singlet sector is posited (SO-1).** No theorem derives the entangled
preparation. The dependency runs: assumed singlet sector → derived kernel and
volume realisation → Bell violation → forced failure of setting-local product
outcomes. C1 must not claim CSD derives the origin of the entangled sector.

**General no-signalling over a non-factorising `Σ` is OPEN.** Sufficient
primitive conditions that *imply* remote marginal invariance are unknown; see
the `specs/BACKLOG.md` row. The measure-level predicate is close to a
restatement of the conclusion, so §4.2 of C1 is a **verification of
no-signalling in the constructed sector, not a derivation from primitives**, and
should say so in those words.

**Measurement independence is assumed.** `OperationalNoSignalling` fixes one `μ`
across all four contexts, and that fixture *is* measurement independence — a
genuine Bell premise, named explicitly in the module rather than left implicit.

**Type separation proves nothing.** The earlier claim that
`ContextIndexedOutcomeMaps` and `GlobalCHSHAssignment` "being different types
carries the Bell-consistency content" was **false** and is corrected in
`LF3/ContextMap.lean`. Different structures give definitional separation only.
Worse, the per-context domains *prevented* the no-go from being stated; it
becomes expressible only on a shared domain.

**`nudgedSinglet` is not a local-unitary image of the singlet.** Its coordinates
are the real non-negative `√P_st`, all phase discarded, making it a **product
state** at `a ⊥ b` where the singlet is maximally entangled. The earlier
docstring saying otherwise was false and is corrected. Use `localNudgeVec`.

## Claim status, explicitly (work-order item 27)

Theorem strength is stated per claim, so nothing inherits a neighbour's status.

| Claim | Status |
|---|---|
| Bell CHSH bound | **proved** (`lhvCHSH_abs_le_two`) |
| Singlet Bell violation | **proved** (`chsh_singlet_at_optimal_angles`) |
| No setting-local product reproduction | **proved** (`no_product_partition_realises_singlet`), every setting pair |
| Shared-domain C1 compatibility obstruction | **proved** (`no_compatible_global_chsh_assignment_realises_singlet`), four CHSH settings only |
| Local de-isolation coupling | **proved** (`localDeisolation_factorises`) |
| Local nudge | **proved, and a CORRECTION** — the original claim about `nudgedSinglet` was false; `localNudge` is the repair |
| Full local measurement chain | **proved** (`localMeasurementChain_factorises`), composing the two above |
| Pointer-volume reproduction, generic contexts | **proved** with `hgen` (`localDeisolation_pointer_volume`) |
| Pointer-volume reproduction, **all settings** | **proved without `hgen`** (`localDeisolation_pointer_volume_local`), including `a·b = ±1` |
| No-signalling, kernel level | **proved** (`singlet_operational_no_signalling`) |
| No-signalling, LF6 pointer-volume construction | **proved** (`localDeisolation_no_signalling_A/B`), marginal volumes, under measurement independence |
| Arbitrary non-factorising Σ no-signalling | **OPEN** — `specs/BACKLOG.md` row; no axiom added |
| Singlet sector origin (SO-1) | **assumed / open** — posited, never derived |

**Headline status (updated 2026-08-10, after promotion).**
`no_compatible_global_chsh_assignment_realises_singlet` **is now CL-031**, a row
in `CsdLean4/Headlines.lean` and `specs/validation-claims.tsv`, which now carry
**31** CL-numbered claims. It sits beside CL-020 and CL-021, the other Bell
no-gos, and its `finding` column records that it arrived through this correction
and replaces the false type-separation claim.

The locality and no-signalling results remain **sub-headline formal support**,
deliberately: the local-de-isolation tier they extend is itself unlisted, so
promoting successors above their predecessors would make the ledger less
coherent. Their axiom pins live in the namespace-matched audit parts, so they
are gated regardless of ledger status.

## References

`specs/c1-correction-plan.md` (the correction's plan and findings);
`specs/necessity-audit.md`; `CsdLean4/Headlines.lean`;
`scripts/check-claim-provenance.sh` (the guard added to catch the two failure
modes this correction found).
