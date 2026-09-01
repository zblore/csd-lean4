# Lieb → DPI — scoping the last rung of the operator-convexity ladder

**Status:** scoping only, written 2026-09-01 on request ("plan this: Lieb → DPI"). No Lean landed
from this document. Walls checked first, on the Q10 mold, because the Q12 arc cost three
restatements by starting work before checking them.

**What it asks.** Discharge the explicit `hDPI` hypothesis of
`QuantumInfo.strong_subadditivity_of_relEntropy_monotone`
(`Mathlib/QuantumInfo/StrongSubadditivity.lean`), making strong subadditivity unconditional.
`hDPI` is data-processing for a single partial trace, stated entirely in corpus vocabulary:

```lean
(hDPI : ∀ (hpdA' : (partialTraceRight (rhoAB ρ)).PosDef),
    relEntropy (rhoAB_posSemidef hpsd).1 (Matrix.PosDef.kronecker hpdA' hpdB).1
      ≤ relEntropy hpsd.1 (Matrix.PosDef.kronecker hpdA hpdBC).1)
```

**The payoff, stated exactly, because it is smaller than the effort implies.** Two things.
`CL-023` moves from `qualified` to validated (its `load_bearing` field is literally "explicit
hDPI premise"). And `Empirical/QM/NoBroadcasting.lean`'s full BCFJS commuting-states *iff*
unlocks — that file's gate was corrected on 2026-08-30 from "fidelity" to `hDPI`. Nothing else
in the corpus is gated on it.

⚠️ **And the first of those two is weaker than it sounds.** `CL-023`'s ledger finding reads
*"confirmed qualified-by-design (the qualification is the claim's permanent scope)"* — it is one
of 19 rows at their **correct terminal status**. The repo's own rule is that by-design rows are
never counted as promotable. So discharging `hDPI` would not close a gap on `CL-023`; it would
*change what the claim is*. **The entire hard payoff is therefore BCFJS in `NoBroadcasting.lean`,
plus a stronger-sounding SSA.** Every cost below should be weighed against that, and it is a
small prize.

---

## 1. ★ Wall-check, done before any theorems

### W1 — the cheap half of the ladder is finished, and came in far under budget

`specs/operator-convexity-plan.md` is **one tranche stale** (it does not mention the landed
names at all). Actual state:

* **L.2** operator concavity of `log` — LANDED 2026-09-01 (`Matrix.operatorConcaveOn_log`).
* **L.3a interior** `x^p`, `p ∈ [0,1]` — LANDED (`Matrix.matrix_rpow_concave`).
* Both were **transports**, not builds: upstream had proved the C⋆-generic statements in April
  and the "Matrix is not a CStarAlgebra" wall was a *scope* question.
* **L.4** `x log x` operator convex — ★ **PROVED 2026-09-01 in a scoping probe**, compiling,
  ~40 lines (`scratchpad/probe_c.lean`, `CFC.convexOn_mul_log`). Its prerequisite, `x^p`
  operator convex on `Icc 1 2`, is proved in the same probe. **Both close named upstream
  Mathlib TODOs verbatim** (`ExpLog/Order.lean`, `Rpow/Order.lean`).

The cheap route mattered: `x log x` does **not** need a new uniform-convergence lemma. It is
`Tendsto.const_mul` on the *existing* `CFC.tendsto_cfc_rpow_sub_one_log`, then
`isClosed_setOfPred_convexOn.mem_of_tendsto` — the same shape as `CFC.concaveOn_log`.

### W2 — the summit has no Mathlib precedent, and the plan's sizing is not achievable

Exhaustive search of the pin: **zero hits** for Effros, perspective, Lieb, Ando, Kubo, Kubo–Ando
means, Hansen–Pedersen, operator Jensen, Epstein, Wigner–Yanase, Golden–Thompson, operator
geometric mean, quantum relative entropy. The upstream operator-convexity tier is **entirely
one-variable**; every two-variable result is absent.

⚠️ **`specs/operator-convexity-plan.md`'s "4–7 working weeks beyond L.1" is not achievable and
should be retired.** It was written before the summit's shape was known. Honest re-estimate for
a genuine in-corpus route: **3–5 months** of focused work for a fluent Mathlib author, with
meaningful tail risk of 6+ months concentrated in operator Jensen and the perspective.

### W3 — nothing is coming from upstream Mathlib

Zero open or merged PRs, zero issues, on Lieb / operator Jensen / perspective / quantum relative
entropy / SSA / DPI (Mathlib's only DPI is classical KL). The operator-convexity stratum is one
contributor's work (@dupuisf, six PRs, 2025-07 → 2026-04-29) and **that line stopped four months
ago at exactly the rung below `x log x`** — the TODO this scoping probe just closed. The one
nearby open PR is a `LLM-generated`-labelled draft, untouched since it opened.
**"Wait for upstream" has no evidence behind it.**

### W4 — ⛔ the deciding wall: it is already proved, on our exact pins

`leanprover-community/physlib` proves **unconditional** strong subadditivity:
`QuantumInfo/Entropy/SSA.lean` → `Sᵥₙ_strong_subadditivity`; and
`QuantumInfo/Entropy/DPI.lean` → `qRelativeEnt_joint_convexity`, which is *precisely* the deep
input `hDPI` encodes. `ForMathlib/HayataGroup/TraceInequality/` carries the whole
operator-convexity stratum this document sizes at 3–5 months (`OperatorConvexOn`,
`JensenOperatorInequality`, `LownerHeinzTheorem`, `GeneralizedPerspectiveFunction`,
`LiebAndoTrace`), ported from `Hayata-Yamasaki-Group/lean-quantum` (arXiv:2607.05492).

**Verified directly, not inferred** (their `lake-manifest.json`): physlib pins
`leanprover/lean4:v4.33.0` and resolves mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d` — **byte-identical to `csd-lean4`**. The toolchain
objection that ruled out Lean-QIT in the 2026-07-31 decision **does not apply here**. (Lean-QIT
itself is unchanged: still Lean 4.30.0, no bump since 2026-05-26.)

⚠️ **Why this was not known:** `specs/external-library-map.md`'s 2026-08-17 rescan recorded
"0 hits" for density matrices, channels, POVMs, partial trace, entropy in physlib. That is a
**verified false negative, retracted 2026-09-01** — the scan grepped *our* vocabulary against a
library spelling those `HermitianMat`, `traceLeft`/`traceRight`, `Sᵥₙ`, `qRelativeEnt`. Its
module count was right, so it enumerated the files and the search missed them.

---

## 2. ★ What the wall-check reshapes

The row is not "build Lieb → DPI". It is **"choose between building and depending, where the
numbers are lopsided and one option was hidden by a bad grep."**

| Route | Cost | What it buys | Verdict |
|---|---|---|---|
| **(a) Build the summit in-corpus** | **3–5 months**, tail 6+ | `hDPI` discharged with a Mathlib-only footprint | Reclimbing a mountain that exists |
| **(b) Bridge to physlib** | **days**, plus a *permanent* pin-coupling tax (§3b) | same two consequences | Viable; **but see §3b — a poor first use** |
| **(c) Wait for Mathlib** | — | — | Reject: no PRs, no issues, contributor stopped |
| **(d) Bridge to Lean-QIT** | M–L | same | Superseded: still 3 Lean versions behind |

---

## 3. Bricks, in order, with gates

### Gate 0 — ⚠️ THE AXIOM GATE, still open

Everything below is conditional on physlib's SSA having the foundational-triple footprint.
**Static analysis only so far**: the SSA import cone is 56 `QuantumInfo` modules and is
`sorry`-free (the three `sorry` hits in `ForMathlib/HermitianMat/CFC.lean` are inside `--`
comments — checked after a coarser scan flagged them).

⚠️ **`#print axioms Sᵥₙ_strong_subadditivity` has NOT been run.** A build was attempted and
failed at 8745/8761 with a Windows *filesystem* error — `failed to create file
'…RingInverseOrder.olean.server'` — from the long scratchpad path, **not** a Lean or physlib
error. Re-run from a short path (e.g. `C:\zayn\physlib`). Physlib's lakefile sets
`-Dwarn.sorry=false` on the `QuantumInfo` target, so a green build is **not** sufficient; the
`#print axioms` pin is the real gate. **If the footprint is not `[propext, Classical.choice,
Quot.sound]`, route (b) is off and this document is void.**

### Gate 1 — is SSA-unconditional actually consumed?

`BACKLOG.md`'s row is marked *"Deferred by user 2026-07-23"*. This scoping collapses the **cost**;
it does not make the **need** appear. §"payoff" above is the whole of it: one ledger promotion
plus BCFJS. **Decide this before spending days, not after.**

### Route (b) bricks — `csd-qit-bridge`, against physlib

The 2026-07-31 architecture stands unchanged: a separate package depending on both **by tag**,
adapter outside `CsdLean4`, neither project merges, `CsdLean4` keeps its Mathlib-only footprint.
Vendoring stays rejected.

| # | Brick | Rating | Note |
|---|---|---|---|
| P1 | New package, both deps by tag | S | no version negotiation — identical pins |
| P2 | `Matrix ↔ MState` packing | S | `MState` bundles exactly our `PosSemidef` + `trace = 1`; **partial-trace index formula is identical**, entropy formula identical, same log base |
| P3 | Match `assocE`/`reassocABC` to `MState.assoc'` | S–M | ⚠️ orientation not checked — the one real unknown in the cheap route |
| P4a | **Cheap route:** export unconditional SSA | S | their `Sᵥₙ_strong_subadditivity` gives our *conclusion* directly; never constructs an `hDPI` term |
| P4b | **Full route:** produce `hDPI` proper | M | needs their `ENNReal`-valued `𝐃` converted to our ℝ-valued `relEntropy` under the `PosDef` support condition (finite there, so tractable) |

**Choose P4a or P4b by whether you need the hypothesis discharged or just the theorem.**

### Route (a) bricks — retained only as a fallback record

B7 **operator Jensen / Hansen–Pedersen** `f(V*AV) ≤ V*f(A)V` — **L**, no Mathlib precedent, no
cheap substitute; the 2×2 unitary dilation is the work. B8 **perspective + Effros joint
convexity** — **L**. Then B6 `cfc f (1 ⊗ₖ ρ) = 1 ⊗ₖ cfc f ρ` (M), B9 the perspective identity
(M), B10 joint convexity in the corpus's proof-indexed `relEntropy` shape (M), B11 unitary
invariance (S–M), B12 tensor additivity (S–M, `cfc_log_kronecker` landed), B13 **general-`d`
Weyl/clock–shift twirl (M — the corpus's `Pauli.lean`/`Clifford.lean` are qubit-only and NOT
reusable; `Fourier.lean`'s root-of-unity orthogonality is the starting point)**, B14 assembly (M).

**Highest-risk brick: B7.** If it slips, everything downstream slips.

**The route that avoids B7:** Kubo–Ando geometric mean via the Schur max-characterisation
`A # B = max { X = X* : [[A,X],[X,B]] ≥ 0 }`, which makes joint concavity immediate from
convexity of the PSD cone — *literally* the `PosDef.fromBlocks₁₁` engine already written for L.1.
It trades B7 for a whole operator-mean API (**L–XL**, cheaper individual steps). If route (a) is
ever taken, spike this for one week before committing to B7.

⛔ **Frenkel's integral formula (Quantum 7, 1102) was chased and rejected**: its DPI step is
nearly free here (the corpus's `DataProcessing.lean` already has the identical variational
argument for trace distance), but the *formula* needs residue calculus on `det(A(t)+r·1)` with an
implicit-function change of variables along an algebraic curve. **XL**, the wrong trade.

---

## 3b. ★ Is a bridge good long-term architecture?

Asked directly during scoping, and it deserves a straight answer rather than an implicit one.

**First, a framing correction.** The recommendation is *not* "integrate physlib". It is a
**separate package that depends on both**; `CsdLean4` gains no dependency and keeps its
Mathlib-only footprint. That distinction is the whole architecture, and it was already the
2026-07-31 design — this scoping only changes *which* library the bridge points at.

**Where the pattern is sound.** For a result you want to *cite and check* rather than build on,
a by-tag bridge is a good pattern: the foundations repo stays self-contained and axiom-audited,
the external result is pinned and re-checkable, and nothing in the main corpus depends on
someone else's release cadence. Vendoring stays correctly rejected.

**The permanent tax, which is the honest cost.** Byte-identical pins today are *luck, not
guarantee*. `CsdLean4` bumps on its own schedule; physlib bumps stable-only, ~8 days after
release. Every bump opens a window where the bridge does not build, and it closes only when both
sides land. That tax is forever, it is paid by whoever maintains the bridge, and it buys nothing
during the window. ⚠️ The 2026-07-31 decision rejected Lean-QIT for exactly this and was right to;
physlib is not immune, it is merely *aligned right now*.

**The audit question does not go away, it goes implicit.** Vendoring was rejected because 60,800
lines of unfamiliar code is too much to audit to a zero-axiom standard. Depending on physlib
means *relying* on a 56-module / ~29,200-line cone that has not been audited to that standard
either. `#print axioms` bounds the trusted base, which is real and worth a lot — but it is not
the same as the line-by-line posture the rest of this corpus is held to.

**The failure mode to name explicitly.** A bridge is fine as *one* exception. It is corrosive as
a *policy*: if "Mathlib lacks X" starts routing to "bridge to whoever has X", the repo's
self-containment becomes fictional while still being claimed. That is a documentation-honesty
risk of exactly the kind the residue registry and the absence guard exist to prevent.

**★ The option that dissolves the question.** The operator-convexity stratum is absent from
Mathlib because *one contributor stopped in April*. This session closed two of the named TODOs he
left. The Hayata group has the rest, Apache-2.0, with a paper. If that stratum went upstream,
**nobody needs a bridge** — not this repo, not physlib, not Lean-QIT — and the dependency
question disappears rather than being managed. That route is currently blocked by an internal
decision, not a technical one: B6 (Mathlib PRs) was retired 2026-08-06 as "not a need of this
repository". ⚠️ That retirement was made when PRs looked like altruism. This is the first case
where a PR would *remove a wall the corpus is standing behind*, which is a materially different
argument, and is worth putting back in front of the author rather than treating as settled.

**Net.** The bridge is *acceptable architecture* and a *poor first use*: the tax is permanent and
the prize here is one `iff` in `NoBroadcasting.lean`. See the recommendation.

## 4. Non-goals

* **Not** vendoring physlib. Depend, or do nothing.
* **Not** adding a dependency to `CsdLean4` itself. The bridge is a separate package; the
  Mathlib-only footprint is the point of the architecture.
* **Not** upstreaming the probe lemmas as PRs — B6 (Mathlib PRs) was retired 2026-08-06 by
  author decision. Staging them Cat-1 is code hygiene and remains in scope; PRing is not.
* **Not** re-deriving what physlib has, in order to own it. If provenance of unconditional SSA
  matters more than having it, that is a *values* decision and should be recorded as one, not
  smuggled in as a technical estimate.

---

## 5. Recommendation

★ **Revised after the payoff and architecture analysis above: the recommendation is NOT to build
the bridge now.** Do 1 and 2; treat 3 as a genuine decision point that probably resolves to "no".

1. **Land the two probe lemmas** (`CFC.convexOn_mul_log`, `CFC.convexOn_rpow` on `Icc 1 2`) as
   staged Cat-1. ★ **This is the one no-regret action**: they are proved and compiling, they
   close two named upstream TODOs, they complete L.4, and they are worth having on **either**
   route. ~200 lines including the `Matrix` transport.
2. **Run Gate 0** from a short path. Cheap, decisive, and everything else waits on it.
3. **Answer Gate 1.** If SSA-unconditional is not actually consumed, stop here — the honest
   outcome is a corrected `operator-convexity-plan.md` and no further work.
4. **If it is consumed: route (b), P1→P4a**, which is days — but read §3b first, because the
   bridge's cost is a permanent maintenance coupling and the prize is one `iff`. **The
   likeliest correct answer is to keep `hDPI` honest and do nothing**, which is what the corpus
   already does and documents well.
5. **Separately, and independently of all of the above: put B6 back in front of the author.**
   Upstreaming the operator-convexity stratum is the only route that makes the dependency
   question disappear instead of managing it forever, and this session produced two Mathlib-ready
   pieces of it.
6. **Retire the "4–7 working weeks" sizing** in `operator-convexity-plan.md` and record the
   3–5 month figure against route (a), so the comparison is never re-litigated from stale numbers.

**The honest headline:** the ladder's cheap half is finished and came in under budget; its
expensive half is an order of magnitude over the recorded estimate; and the result already
exists, sorry-free, on byte-identical pins, in a library this repo had already classified as
having nothing to offer.

## References

`specs/operator-convexity-plan.md` (stale sizing, L.2/L.3a not recorded);
`specs/BACKLOG.md` row "Operator convexity → unconditional SSA" (the 2026-07-31 decision) and
the `SSA / DPI via Lean-QIT` row; `specs/external-library-map.md` (the retracted 2026-08-17
false negative); `CsdLean4/Mathlib/QuantumInfo/StrongSubadditivity.lean` (`hDPI`);
`CsdLean4/Mathlib/Analysis/Matrix/OperatorConvexBridge.lean` (L.2/L.3a, landed);
`CsdLean4/Empirical/QM/NoBroadcasting.lean` (the other consumer);
`specs/validation-claims.tsv` CL-023. External: physlib `QuantumInfo/Entropy/{SSA,DPI}.lean`;
`Hayata-Yamasaki-Group/lean-quantum` (arXiv:2607.05492); Frenkel, *Quantum* **7**, 1102 (2023).
