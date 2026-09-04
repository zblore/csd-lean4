# Publication errata and debts

Claims in **manuscripts that are not editable from this repository** which the
formal work has since shown to be wrong or overstated. Created 2026-08-10.

This file exists so that a defect found in the Lean is not quietly fixed in the
Lean alone while the published or circulating text keeps asserting it. Fixing a
docstring does not fix a paper.

Each entry records: what the text claims, why it is wrong, what the repository
now says instead, and what the paper must do.

---

## E-1 — LF3 §8.7 / §9.9: type separation does not carry Bell content

**Status:** OPEN (paper edit required; the repository side is corrected).
**Found:** 2026-08-10, during the C1 correction.
**Repository side re-verified 2026-08-19:** clean. `LF3/ContextMap.lean:18,55`,
`specs/LF3-plan.md:820`, `specs/lf6-plan.md:9` and `docs/C1-FORMAL-SUPPORT.md:83,123`
all carry the correction; the surviving `§8.7`/`§9.9` strings are section *pointers*,
not restatements of the false argument. Nothing further to fix here — this entry is
now **manuscript-only**.

**What the text claims.** That `ContextIndexedOutcomeMaps` and
`GlobalCHSHAssignment` being *different data types* carries the
Bell-consistency content, and that no Fine-theorem axiom is therefore needed.
`LF3/ContextMap.lean` attributed this framing to Paper §8.7 / §9.9, and the same
wording appeared in `specs/LF3-plan.md`.

**Why it is wrong.** Different structures establish only **definitional**
separation. Type distinctions are stipulations, not discoveries: choosing to
model two things as different types encodes an intuition and proves nothing.
A no-go must come from a theorem quantifying over the objects.

Worse, and this is the part the paper most needs to absorb: the separation did
not merely fail to prove the no-go — it **prevented the no-go from being
stated**. Because `ContextIndexedOutcomeMaps` gives each context its own
`Domain ctx`, there is nothing to compare against a global assignment on one
state space. The modelling choice made the Bell question inexpressible, which is
why the missing theorem went unnoticed for so long.

**What the repository now says.** `LF3/ContextMap.lean` and
`specs/LF3-plan.md` state that type separation alone does **not** prove
incompatibility, and name the theorems that do the work:

* `LF6.no_product_partition_realises_singlet` — over any shared probability
  space, at every setting pair;
* `LF6.no_compatible_global_chsh_assignment_realises_singlet` — on **one shared
  state space**, at the four CHSH settings, which is the shape C1 actually
  posits and which only became statable once the shared domain replaced the
  per-context ones.

**What the paper must do.** Delete the type-separation argument. Replace it with
a citation to the repository at a tagged release (commit SHA, module path,
theorem name). Do not present the structural distinction as carrying
mathematical content; it may be retained, if wanted, as an explicitly labelled
modelling intuition.

---

## E-2 — the "nudge" is not a local basis rotation

**Status:** OPEN (paper edit required; the repository side is corrected **as of
2026-08-19 — it was not before**).
**Found:** 2026-08-10.

⚠️ **Repo-side residue found and fixed 2026-08-19.** This entry claimed the
repository side was corrected; that was true at the *definition* site
(`SingletDeisolationFlow.nudgedSinglet`, `NudgeLocality.lean`,
`ForcedContextuality.lean:76`) but **two prose blocks in
`CsdLean4/LF6/LocalDeisolationFlow.lean` still asserted the falsified reading** —
`localDeisolation_pullback`'s docstring said the axis context was "carried by the
`nudgedSinglet a b` rotation" and that the computational projectors were "the
physical eigenprojectors expressed in the rotated frame", and
`localDeisolation_pointer_volume`'s said `φ = nudgedSinglet a b` was "the singlet in
the rotated axis-context basis". Both now state the correct reading (the preparation
carries the context through its setting-dependent moduli `√(P_st a b s t)`; no
rotation is invoked) and both point at `LF6.localNudgeVec`. No proof changed — the
statements consume only `‖·‖²` — and the full tree stays green (4013 jobs).
**Lesson for this file: "the repository side is corrected" needs a grep across every
consumer, not just the definition site.** The prose-audit defect class
(`specs/prose-audit.md`) is exactly this: a false claim that survives only in prose,
downstream of a corrected definition.

**What the text claims.** That the prepared state is the singlet in the rotated
axis-context basis, `(U_A ⊗ U_B)† ψ⁻` — a *local* basis rotation.

**Why it is wrong.** The formal object `nudgedSinglet a b` has coordinates
`√(P_st a b s t)`: real, non-negative, **every relative phase discarded**. Local
unitaries preserve Schmidt spectra and `ψ⁻` is maximally entangled; but at
`a ⊥ b` all four `P_st = ¼`, so the object is `½(1,1,1,1)`, a **product state**.
No local unitary carries a maximally entangled state to a product state. It is a
local-unitary image of the singlet only at `a·b = ±1`, precisely the endpoint
set the genericity hypothesis excluded.

The cause: `singletJointEig` normalises by the real `√P_st`, fixing each basis
vector's phase by projecting `ψ⁻` itself. That is four independent phases where
a product unitary supplies only separable ones.

**What the repository now says.** `nudgedSinglet`'s docstring states plainly
that it is the moduli, not a rotated singlet, and directs readers to
`LF6.localNudgeVec`, which *is* defined as `(U_A(a) ⊗ U_B(b))ᴴ ψ⁻` for the
proved-unitary `wingBasisUnitary`, carries the same Born statistics, and needs
no genericity hypothesis.

**What the paper must do.** Either cite `localNudge` / `localNudgeVec` and its
Born identity, or state only that the construction reproduces the Born
*probabilities* and drop the claim that it does so by a local rotation. The
chain-locality claim is available, but only through the corrected object
(`localMeasurementChain_factorises`).

---

## E-3 — Paper D §8: PBR's target is stated backwards, and two senses of "epistemic" are run together

**Status:** OPEN (paper edit required; the repository side is correct and was
never wrong). **Raised:** 2026-09-04, during an external review of the §0
report. ⚠️ **Reported, not verified here:** the manuscripts are not in this
repository, so the reviewer's reading of §8 is taken as given. What IS verified
is everything the repository side asserts below.

**What the text is reported to claim.** That PBR targets ψ-**ontic** models, and
that CSD's "epistemic" reading of the state puts it on the side PBR rules out.

**Why it is wrong.** The Harrigan–Spekkens classification runs the other way. A
preparation interface is ψ-**ontic** when distinct exact pure preparations have
**mutually singular** ontic measures, ψ-**epistemic** when some distinct pair
overlaps; PBR rules out the **ψ-epistemic** class (under preparation
independence). CSD's exact sharp interface is on the ψ-**ontic** side, so it
*satisfies* PBR's disjointness conclusion rather than being a target of it.

The conflation underneath is between three distinct claims, which
`RecordLayer/PBRPreparation.lean` was written to separate and which its header
lists in order:

1. **CSD epistemicity of `[ψ]`** — `π : Σ → ℂℙ^{N-1}` is many-to-one and
   incomplete. This is the corpus's own sense of "the state is epistemic".
2. **Harrigan–Spekkens ψ-onticity** — the technical classification above. CSD is
   ψ-ONTIC here.
3. **Finite-resolution preparation overlap** — positive-volume *region*
   preparations with overlapping regions provably DO have non-mutually-singular
   conditional laws.

(1) and (3) are true; (2) says CSD is ψ-ontic on the exact interface; there is no
tension, because they are claims about different objects. The module's own
verdict: *"Conflating (3) with (2) was the error this module corrects."*

**What the repository now says.** ★★ `sharp_preparations_mutuallySingular`
(`RecordLayer/PBRPreparation.lean:141`) — any two ontic measures whose projective
laws are Diracs at distinct points are mutually singular, with no `Preparation`
structure, no region and no finiteness in the hypotheses. Concrete corollary
`epistemicMeasure_mutuallySingular` (:163); capstone
`pbr_sharp_preparation_capstone` (:258); class separation
`exact_sharp_ne_region_conditional`. `Mathlib/MeasureTheory/MutuallySingularMap.lean`
is the Cat-1 measure-theory input (`Measure.MutuallySingular.of_map`), **not** the
result itself — a citation naming that file for the ψ-onticity claim is naming the
wrong thing.

⚠️ Two riders the paper must keep. **Nothing in the corpus bears on PBR
preparation independence** — PI is neither established nor refuted, and the
module says so explicitly. And the **earlier non-factorisation defence is
withdrawn**: reading the Segre composite-geometry results as a PBR contradiction
was the superseded Q28 interpretation (`specs/c2-support-plan.md`).

**What the paper must do.** State the classification in the Harrigan–Spekkens
direction; say that CSD's exact sharp interface is ψ-ontic and cite
`sharp_preparations_mutuallySingular`; keep the corpus's sense (1) of "epistemic"
verbally distinct from the classification; mention (3) rather than leaving a
referee to find it; and assert nothing about preparation independence.

---

## E-4 — Paper D §8: the equivariance analogue is posited on one side, not "proved twice"

**Status:** OPEN (paper edit required; the repository side is correct as stated,
but is easy to over-read). **Raised:** 2026-09-04, same review. ⚠️ Same caveat:
the §8 text is reported, not read from here.

**What the text is reported to claim.** That CSD's analogue of Bohmian
equivariance is *proved twice* — Liouville preservation of `μL` under the ontic
flow, and invariance of `μ_FS` under the projective unitary flow.

**Why it is wrong.** The two halves have different status.

* `μ_FS` invariance IS a theorem: `fubiniStudyMeasure_smul_invariant`
  (`Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean:165`), with
  `kFlow_measurePreserving` (`LF4/KahlerFlow.lean:86`) the constructed instance.
* `μL` preservation is **not a theorem**. It is a **field of the structure** —
  `ConstraintDynamics.flow_preserves`, P4: *"each time-`t` map preserves the
  Liouville measure"*. It is posited of every model, not derived in any.

The distinction is exactly the one a Bohm comparison turns on. In Bohmian
mechanics equivariance is a theorem, obtained from the guidance equation with the
continuity equation. In CSD the corresponding preservation is structural. That
does not weaken the comparison — it sharpens it, and it is why the origin of the
measure remains a posit on both sides, which is the paragraph's own conclusion.

Related: the "Dirac on the base, Haar on the fibre" preparation
(`epistemicMeasure p = δ_p ⊗ vol`) is **covariant, not invariant** — the shape is
preserved while the base point transports. And there is at present **no single
named theorem** stating the equivariance analogue, which is why the comparison
keeps being lost; a capstone stating it is a candidate Lean brick, not an
existing result. `isolated_flow_measure_preserving`, cited in the review draft,
does not exist.

**What the paper must do.** Say "posited once, proved once", naming
`ConstraintDynamics.flow_preserves` (P4) and `fubiniStudyMeasure_smul_invariant`;
or, if a single citation is wanted, cite `kFlow_measurePreserving` as the
constructed instance and say that the general preservation is structural.

---

## How to use this file

Add an entry whenever formal work contradicts or materially weakens a claim in
text that cannot be corrected from here. Close an entry only when the text is
actually amended — not when the repository side is fixed.

## References

`specs/c1-correction-plan.md`; `docs/C1-FORMAL-SUPPORT.md`;
`CsdLean4/LF3/ContextMap.lean`; `CsdLean4/LF6/NudgeLocality.lean`;
`CsdLean4/LF6/SingletDeisolationFlow.lean`; `CsdLean4/RecordLayer/PBRPreparation.lean`
and `specs/c2-support-plan.md` (E-3); `CsdLean4/SigmaLayer/ConstraintDynamics.lean`,
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean` and
`CsdLean4/LF4/KahlerFlow.lean` (E-4).
