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

**Status:** OPEN (paper edit required; the repository side is corrected).
**Found:** 2026-08-10.

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

## How to use this file

Add an entry whenever formal work contradicts or materially weakens a claim in
text that cannot be corrected from here. Close an entry only when the text is
actually amended — not when the repository side is fixed.

## References

`specs/c1-correction-plan.md`; `docs/C1-FORMAL-SUPPORT.md`;
`CsdLean4/LF3/ContextMap.lean`; `CsdLean4/LF6/NudgeLocality.lean`;
`CsdLean4/LF6/SingletDeisolationFlow.lean`.
