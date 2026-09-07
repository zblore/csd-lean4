# Quantum Darwinism / record redundancy: scoping note

**Status:** SCOPED 2026-09-07; **QM side BUILT the same day** (`Empirical/QM/Darwinism.lean`,
5 pins). **CSD side NOT BUILT.** Expert-review row **E** of [`BACKLOG.md`](BACKLOG.md).

**As landed (QM side):** `SpectrumBroadcast` (§2b), ★ `not_of_constant_fragment` — §4's
vacuity test *as a theorem*, ★ `successProb_eq_one_of_discriminating`, the witness
`copyBroadcast` and ★★ `copyBroadcast_perfect` (every fragment, on its own, identifies the
outcome with probability one, at arbitrary `k`). §2's rejection of the entropic form is
recorded in the module header with its reason.

⚠️ **One deviation from §6, recorded.** §6 asked for `sbs_fragment_determines_outcome` as a
theorem about *every* `SpectrumBroadcast`. Building it showed that deriving the discriminating
test from `ρᵢρⱼ = 0` alone needs the **support projection** of a positive semidefinite matrix
and a lemma that it annihilates orthogonal states — a spectral argument, and
`TraceDistance.lean` has `posProj` but not that lemma. What landed instead is the conditional
lemma (`successProb_eq_one_of_discriminating`, hypotheses about the test, not about
discriminability — so §4 is respected) plus its instantiation on the witness, where the
projection is explicit. **The general theorem is the residue**, recorded in the module's own
honest-scope block.

⚠️ **NOT `csd-foundations`-checked.** Every comparable note in this directory
([`ozawa-scoping.md`](ozawa-scoping.md), [`local-friendliness-scoping.md`](local-friendliness-scoping.md),
[`generation-from-records-scoping.md`](generation-from-records-scoping.md)) records a
`csd-foundations` pass with its findings folded in. That agent was not available in the
session this was written in, so this note has had **one pair of eyes, not two**. Run the
check before the first line of Lean; §2 and §5 are exactly the kind of decision it has
caught before.

⚠️ **Read §2, §3 and §4 before writing any Lean.** §2 is which of three theorems is the
target (one of them is gated behind an open Mathlib wall and must not be picked). §3 is an
arena decision that determines whether this row is **M** or **L**. §4 is the vacuity test
the statement has to pass, and the row's own note flags it: *"the redundancy statement needs
choosing carefully to avoid a placeholder."*

---

## 1. What is being added, and why the corpus wants it

The corpus proves that records are **made**: the pointer strokes
(`RecordLayer/Pointer*.lean`), the Lüders theorems (`PointerLudersMarginal.lean`,
`swap_luders_marginal`), and the closure `RecordLayer/GlobalRecordClosure.lean`, whose
content is that the record event is a function of `(context, outcome, time)` **and of
nothing else** (CL-011). It also has einselection — *which* basis survives
(`Empirical/CSD/Einselection.lean`, `Empirical/CSD/PointerCommutation.lean`).

It says nothing about the record being **copied** into many environment fragments. That is
the gap: in the decoherence literature since Zurek, redundancy is the operational criterion
for a record being *objective*, and objectivity is a claim CSD makes in prose. A referee who
knows this literature will ask, and the answer should be a theorem rather than a paragraph.

⚠️ The answer is **not** that CSD grounds objectivity in redundancy. §5.

## 2. ⚠️ Three theorems wear this name — and one of them is gated

**(a) The mutual-information plateau** (Zurek; Blume-Kohout–Zurek). `I(S : F) ≥ (1−δ) H(S)`
for each of `R_δ` disjoint fragments `F`; the redundancy `R_δ` is the count.

⛔ **Do not pick this one.** It needs mutual information and its monotonicity, and in this
corpus that route is not free: `Mathlib/QuantumInfo/StrongSubadditivity.lean` carries the SSA
reduction with **`hDPI` as an explicit hypothesis**, and unconditional SSA is behind the
Effros/Lieb operator-convexity summit — which is itself behind
[`lieb-dpi-scoping.md`](lieb-dpi-scoping.md) **Gate 1**, an author call
(`BACKLOG.md` ⛔ section). Picking (a) either imports that gate into a breadth row or
re-derives DPI to avoid it. Both are the wrong trade for this row. The δ-parameterised
counting argument on top is bookkeeping, not content.

**(b) Spectrum Broadcast Structure** (Horodecki–Korbicz–Aharonov 2015): the joint
system–environment state **is**

    ρ = Σᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ⁽¹⁾ ⊗ ⋯ ⊗ ρᵢ⁽ᵏ⁾,   with ρᵢ⁽ᶠ⁾ ρⱼ⁽ᶠ⁾ = 0 for i ≠ j.

Structural, entropy-free, and strictly stronger than (a) — SBS implies the plateau, not
conversely. Everything it needs (density matrices, partial trace, orthogonal support,
Kronecker products) is already in `Mathlib/QuantumInfo/`. **This is the QM-side target.**

**(c) Record-level redundancy.** `k` disjoint fragments each carry a record whose value is
the *same* ontic outcome. No Hilbert space, no entropy: a statement about functions on `Σ`.
**This is the CSD-side target**, and it is the twin (b) pairs with.

**Decision: build (b) and (c). Reject (a), and say in both module headers that the
information-theoretic form is the one not built, with the reason** — otherwise the absence
reads as an oversight rather than a gate.

## 3. ⚠️ What a "fragment" is here — the arena decision, and where the cost lives

Two carriers already exist and **neither is right as it stands**:

* **P2 mode concatenation** (`CV/CompositeArena.lean`): the composite of a `K₁`-mode and a
  `K₂`-mode sector is the `(K₁+K₂)`-mode sector, which generalises to `k` blocks for free.
  ⚠️ But P2 exists to carry the **algebra forcing** (`compositeAlgReconstruction`), not
  records; nothing there reads a record off a block.
* **The pointer bank** (`RecordLayer/PointerLuders.lean`): the arena `(Σ × ℂℙᴺ) × bank`
  where `bank` is a `Measure.pi` product with per-slot evaluation
  (`Measure.map_eval_pi'`) and cylinder machinery already in use.
  ⚠️ **Its slots are indexed by OUTCOMES (`Fin N`), not by fragments** — they are the
  calibrated post-measurement states, one per outcome. Treating a bank slot as an
  environment copy is a category error and would produce exactly the placeholder the row
  warns about.

**Recommendation.** Put the fragments on a **new index** `Fin k`, as a `k`-fold product of
pointer factors on the RecordLayer side — a second `Measure.pi`, orthogonal to the bank's.
That reuses the machinery that already works there (product measures, record cylinders,
`measurePreserving_of_partition`) without borrowing the bank's index for a second meaning.
Do **not** build it on the CV side: the CV composite is about algebra, and the record layer
is where records live.

**This is where the rating lives.** If the `k`-fold pointer product goes in as a product of
the existing factor, the CSD side is **M**. If it turns out to need a new arena *species*
(its own invariance lemmas, its own closure), it is **L** — and then the honest move is to
stop and record, not to half-build an arena. §6.

## 4. ⚠️ The vacuity test — apply it to the statement before proving anything

A redundancy theorem is trivially satisfiable. If each fragment's record is **defined** as a
function of the global outcome, then "every fragment agrees with the global record" is a
tautology dressed as physics, and it will typecheck, pin clean, and mean nothing. This is
the failure mode `PLACEHOLDERS.md` exists for.

**The test.** State the theorem, then check it against a **one-fragment stroke**: a dynamics
that writes fragment `0` and leaves fragments `1 … k−1` in their initial state.

* If the theorem still holds — the statement is vacuous. Redo it.
* If it fails — the hypothesis is doing work, and *that* is the theorem's content.

So the statement must quantify over a stroke datum and consume a hypothesis saying each
fragment is coupled by a record-writing interaction. **Non-vacuity therefore needs two
witnesses, not one:**

1. a `k`-fragment stroke that satisfies the hypothesis (the `k`-fold controlled-copy: each
   fragment ends in `ρᵢ⁽ᶠ⁾ = |i⟩⟨i|`, perfectly distinguishable — SBS by inspection);
2. ★ a `k`-fragment stroke that **does not** (the one-fragment stroke above), witnessing that
   the hypothesis excludes something.

Precedent for insisting on (2): `ozawa_two_term_false` and `movingRecords_not_persistent` —
in both cases the refutation is what stopped the positive statement reading as a definition.

## 5. The CSD side: what it must claim, and what it must not

**Must not.** *"Records are objective because they are redundant."* That is Zurek's
grounding, and it is not CSD's. In CSD a record's objectivity is its being an **ontic
selection in `Σ`** — `globalOutcome c x` is a function of the point and the context and of
nothing else, which is what `GlobalRecordClosure` already proves. Redundancy is the
*operational twin* of that fact: what an observer restricted to fragments would find. If the
module says otherwise it inverts the programme's own order of explanation.

**Must.** State the asymmetry positively, because it is a real difference and a referee will
want it: there is **one** trajectory and **one** `Σ`-point. The fragments are not `k` copies
of a classical bit manufactured by decoherence — they are `k` coordinates of a single ontic
point, and the theorem is that they **agree**. Agreement of coordinates of one point is a
weaker and more honest thing than replication, and it is exactly what the ontic reading
predicts.

⚠️ Then say what is *not* thereby shown: nothing here derives that a physical environment
*does* couple this way. Which interaction an apparatus or an environment realises is
`R-015`, a permanent boundary (`POSITS.md` §"three different things"), and the same input
Bohm and Everett take. The `k`-fold copy is a modelling choice, exhibited as a witness.

## 6. Deliverable, and the stop condition

**QM side — `Empirical/QM/Darwinism.lean`:**

* `SpectrumBroadcast` — the structure of §2(b): a probability vector, per-fragment states,
  pairwise orthogonal supports;
* ★ `sbs_fragment_determines_outcome` — from any single fragment's marginal, the outcome is
  recoverable (orthogonal supports ⇒ perfect distinguishability);
* ★ `sbs_redundancy` — the same holds for every fragment independently, which *is* the
  redundancy statement in structural form;
* the two witnesses of §4, one positive and one ★ negative.

**CSD side — `Empirical/CSD/Darwinism.lean`:**

* `fragmentRecord` on the `k`-fold arena of §3;
* ★★ `record_redundancy` — a.e. every fragment's record equals `globalOutcome`;
* ★ the scope theorem of §5: objectivity is the ontic selection, stated so that the
  redundancy theorem cannot be read as its ground (pattern: `no_joint_hilbert_map`,
  `no_ozawa_model_of_jointLift` — a theorem that says what the layer does *not* supply).

**Pins:** every ★ in `Tests/AxiomAudit/`, in the part matching each constant's namespace.

**⛔ Stop condition.** If §3's `k`-fold arena turns out to need its own invariance and
closure lemmas — a new species rather than a product — **stop, record the finding here, and
land nothing.** A partial arena with a redundancy statement resting on it is precisely the
scaffolding `CLAUDE.md` forbids. The QM side (b) is independent of that risk and can land
alone; say so in its header if it does.

## 7. Rating

The row's **M / medium–high / medium–high** is from 2026-09-02 and **predates rows A and C
and brick 3**, so it has not been re-checked against the vocabulary that now exists.

Re-rated here:

| Piece | Cx | P(success) | Note |
|---|---|---|---|
| QM side (b) | **S–M** | High | A structure, an orthogonality argument, two witnesses. Everything it needs is in `Mathlib/QuantumInfo/` |
| CSD side (c), if §3's product works | **M** | Medium–high | Reuses `Measure.pi`, record cylinders, `measurePreserving_of_partition` |
| CSD side (c), if a new arena species is needed | **L** | Low | ⛔ Stop condition, §6 |

⚠️ Both directions of error have precedent in this repository, one each way: **WAY brick 2**
was rated **L** and collapsed to one commutator identity once row B's vocabulary existed,
while **CR-4** was recorded as "no new theorem" and needed seven engine pieces. Re-rate
after §3 is settled, not before.

## References

* Zurek, *Quantum Darwinism*, Nature Physics 5, 181 (2009) — the redundancy criterion.
* Blume-Kohout & Zurek, Phys. Rev. A 73, 062310 (2006) — the mutual-information plateau,
  §2(a), the form deliberately not built.
* Horodecki, Korbicz & Aharonov, Phys. Rev. A 91, 032122 (2015) — spectrum broadcast
  structure, §2(b), the form to build.
* `RecordLayer/GlobalRecordClosure.lean` (`globalOutcome`, CL-011) — the ontic selection §5
  rests on.
* `RecordLayer/PointerLuders.lean`, `RecordLayer/PointerLudersMarginal.lean` — the product
  arena, cylinders and marginal machinery §3 recommends reusing.
* `CV/CompositeArena.lean` — P2 mode concatenation, §3's rejected carrier.
* `Mathlib/QuantumInfo/StrongSubadditivity.lean` — the `hDPI` hypothesis that gates §2(a).
* [`lieb-dpi-scoping.md`](lieb-dpi-scoping.md) — Gate 1, the author call behind it.
* `Empirical/CSD/Einselection.lean`, `Empirical/CSD/PointerCommutation.lean` — the
  neighbouring einselection content this row sits beside.
