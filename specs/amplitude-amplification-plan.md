# Amplitude amplification (Brassard–Høyer–Mosca–Tapp) — scoping and plan

**Status:** scoped 2026-08-29 and **EXECUTED same day (AA-1..AA-4, then the AA-5a slice after
its gate run)** — see the execution record before the references. AA-5b stays gated on the
tensor generalization; AA-6 not scheduled. Gates and abort criteria on the
Q11 mold; walls were pre-checked (the Q12 lesson: probe before rating), and none fired.

**Provenance.** Candidate 2 of the five from the 2026-08-28 algorithms discussion (candidate 1,
QFT + phase estimation extraction, executed 2026-08-29 → `Mathlib/QuantumInfo/Fourier.lean` +
`PhaseEstimation.lean`). The pitch, verbatim: *"Generalises Grover to arbitrary initial success
probability and unknown marked-item count, with Grover falling out as the corollary. It's a pure
amplitude-and-probability theorem — and it's a generalisation rather than another instance,
which is worth more than five more instances."*

---

## 1. What this is, and why it is worth one session

BHMT (Brassard, Høyer, Mosca, Tapp, *Quantum Amplitude Amplification and Estimation*, 2000;
quant-ph/0005055) is the theorem Grover's algorithm is an instance of. Given **any** unitary
preparation whose output has success probability `a = sin²θ` against **any** good set of
outcomes, the amplification operator `Q = (2|Ψ⟩⟨Ψ| − I)(I − 2P_good)` acts on the 2-plane
spanned by the good and bad components as a **rotation by `2θ`**, so `j` applications take the
success probability to `sin²((2j+1)θ)` — exactly, no asymptotics. Choosing
`m = ⌊π/(4θ)⌋` gives success `≥ 1 − a` after `O(1/√a)` applications: the quadratic speedup as a
theorem about one closed form.

Three reasons it is the right next brick, in order of weight:

1. **It is a generalisation, not an instance.** The corpus's `Grover.lean` proves the rotation
   closed form for ONE marked item on the UNIFORM start (`grover_success`). BHMT delivers the
   same closed form for every initial state, every good-set size (the `k`-marked Grover the
   corpus lacks falls out for free), and every preparation unitary — and `grover_success`
   becomes a corollary. One theorem replaces a family of would-be instances.

2. **It is the priced atlas pilot, done on the right target.** The Algorithm Atlas assessment
   (vault, 2026-08-21) ended: *"the only honest test is to do one extraction and measure what
   it cost"* — and separately established (RESULT 4) that the corpus's algorithm layer contains
   duplicated inlined mechanisms and **zero** modern primitives ("amplitude amplification — 0 —
   the phrase appears in Grover's docstring as prose"). AA-3 below is exactly the priced
   extraction: rebuild `grover_success` on the general theorem, delete the parallel
   development, record the hours. Unlike the `AncillaInterference` pilot proposed there, this
   one also *adds* the missing primitive while measuring the refactor cost.

3. **It is what the two open outreach conversations consume.** A quantum Lean library's API
   wants the primitives first (the 2026-08-28 discussion's point). With `PhaseEstimation.lean`
   landed, amplitude amplification is the other half of the standard pair — and the searchable
   Lean ecosystem does not have the general theorem (Lean-QuantumAlg has Grover; checked
   2026-08-29 during the phase-estimation priority check). The Coq side: SQIR verifies Grover;
   whether general BHMT exists there was NOT checked — re-run the priority check before any
   "first" framing, per the CL-061 rule.

**The one-sentence honest position:** this is Cat-1 QM-validity/library breadth, not CSD
thesis work — the standing disclaimer (algorithms consume the unitary pillar) applies from the
first docstring, and the positioning guardrail from the atlas assessment §4 binds: it stays in
the `Mathlib/` tree as library material, it does not become a repository thesis.

## 2. Walls, pre-checked 2026-08-29

* **W-A (Mathlib trig): CLEAR.** `Real.sin_add`/`cos_add` (already consumed by `Grover.lean`'s
  `rot_a`/`rot_b`); `Real.sin_le` (`sin x ≤ x` on `0 ≤ x`) for the query-count reading;
  `Real.arcsin` with `Real.sin_arcsin` and `Real.cos_arcsin` for *constructing* the angle from
  `a` (so the headline can be stated against `θ := arcsin √a` rather than carrying `hsin/hcos`
  hypothesis pairs the way `Grover.lean` does — an API improvement, not just a port).
* **W-B (projections): AVOIDED BY DESIGN.** No need for Mathlib's orthogonal-projection API.
  The good component is the coordinate truncation `i ↦ if i ∈ G then ψ i else 0` on
  `EuclideanSpace ℂ ι` — same `WithLp.equiv` idiom as `mulOracle`/`tensorCN` in `ShorCore`.
  Orthogonality of `G`-supported and `Gᶜ`-supported vectors is a one-line coordinate sum.
* **W-C (complex phases): HANDLED AS IN GROVER.** For complex `ψ` the good/bad unit components
  `g, b` are genuinely complex vectors; the rotation plane is `{(sin γ) • g + (cos γ) • b}`
  with **real** coefficients carried as `ℂ`-coercions — `Grover.lean`'s exact trick, one level
  up. The needed inner products (`⟨g,g⟩ = 1`, `⟨b,b⟩ = 1`, `⟨g,b⟩ = 0`, hence `⟨φ, ·⟩` real on
  the plane) all reduce to coordinate sums.
* **W-D (degenerate boundary): REAL AND MUST BE STATED.** `a = 0` (no good component: `Q` has
  no plane to rotate) and `a = 1` (nothing to amplify) are outside the construction — the
  hypotheses are `0 < a < 1`, honest and load-bearing, mirroring `raceDeIsolationInteraction`'s
  positivity note and Grover's `1 ≤ n`.
* **W-E (the register): ALREADY GENERAL.** The 2026-08-29 R1 generalisation
  (`Register.lean` over arbitrary finite `ι`) is exactly the setting; nothing is
  bitstring-specific. `Finset ι` for the good set gives decidability for free.

No wall is research-grade. The mathematics is `Grover.lean`'s argument executed once at the
right level of generality.

## 3. Bricks, in order, with gates

### AA-1 — the theorem (M; the session's core)

New Cat-1 module `CsdLean4/Mathlib/QuantumInfo/AmplitudeAmplification.lean`:

* `goodProj G ψ` (coordinate truncation), `goodProb G ψ := ∑ i ∈ G, ‖ψ i‖²`;
* `oracleFlip G ψ := ψ − 2 • goodProj G ψ` (the reflection `I − 2P_G`; `Grover.oracle` is the
  singleton instance);
* `reflect φ ψ := (2 * inner ℂ φ ψ) • φ − ψ` (the generalized diffusion `2|φ⟩⟨φ| − I`;
  `Grover.diffusion` is the `φ = uniformState` instance);
* `ampStep φ G := reflect φ ∘ oracleFlip G`;
* the plane family `ampState g b γ := (sin γ : ℂ) • g + (cos γ : ℂ) • b` and the two unit
  components of a state with `0 < goodProb < 1`;
* ★ `ampStep_rotates` — one step advances the angle by `2θ` (the two-reflection rotation, the
  paper's Lemma 1 / the heart);
* ★★ `amplitude_amplification` — the closed form:
  `goodProb G ((ampStep φ G)^[j] φ) = sin²((2j+1)·θ)` with `θ = arcsin √(goodProb G φ)`.

**Gate (before writing):** confirm `Real.cos_arcsin` and `Real.sin_le` exist at pin with the
expected signatures (five minutes; if `cos_arcsin` is absent, fall back to the `Grover.lean`
hypothesis-pair style — costs statement elegance, not feasibility).
✅ **Gate run 2026-08-29, PASS:** `Real.sin_arcsin` (Inverse.lean:61), `Real.cos_arcsin`
(`cos (arcsin x) = √(1 − x²)`, Inverse.lean:245), `Real.arcsin_le_pi_div_two` (Inverse.lean:46),
`Real.sin_le` (`sin x ≤ x` on `0 ≤ x`, Bounds.lean:54) — all present at pin. The arcsin-based
statement form is confirmed available; AA-1 is unblocked.

### AA-2 — the optimal-count corollaries (S–M)

* ★ `amplitude_amplification_succeeds` — for `m = ⌊π/(4θ)⌋`, `(2m+1)θ` lands within `θ` of
  `π/2`, so `goodProb ≥ cos²θ = 1 − a`. This is the bound `Grover.lean`'s own docstring defers
  ("downstream arithmetic on this closed form; not formalised here") — closing a recorded gap,
  not just adding one.
* ★ `amplification_query_bound` — `m ≤ π/(4√a)` via `√a = sin θ ≤ θ`: the quadratic speedup as
  a named inequality.
* Non-vacuity witness at a concrete `a` (e.g. `a = 1/4`: `θ = π/6`, `m = 1`, success `= 1`
  exactly — a pleasant closed instance worth a `#guard`-style example).

### AA-3 — Grover as the corollary, and the priced extraction (S–M; RECORD THE HOURS)

* `groverStep_eq_ampStep` — `Grover.oracle w = oracleFlip {w}` and
  `Grover.diffusion = reflect uniformState`, so the step operators agree definitionally;
* re-derive `grover_success` and `grover_certain` from `amplitude_amplification` (statements
  unchanged — the audit pins in `EmpiricalQM` survive untouched);
* **delete `Grover.lean`'s now-redundant internal development** (`symState` operator lemmas,
  `rot_a`/`rot_b`, `groverStep_rotates`, `groverStep_iterate`) after grepping consumers —
  RESULT 4's lesson: the special-case theorem must not coexist with a full parallel
  development. Keep `symState` itself only if the statement of `grover_success` still wants it
  (it does not — the statement mentions only `groverStep`, `uniformState`, `prob`);
* ★ NEW `grover_multi_success` — the `k`-marked corollary on the uniform start
  (`G` of size `k`, `a = k/N`): the standard generalisation the corpus lacks, free at this
  point;
* **record the wall-clock cost of this brick in the module header** — it is the atlas
  assessment's requested pilot number (cost per extracted mechanism).

**Abort criterion for the deletion half:** if re-deriving `grover_success` from the general
theorem fights the `ℂ`-coercion seams for more than ~an hour, keep both developments
temporarily, land the general module, and file the refactor as its own small item — landing
AA-1/AA-2 must not be hostage to the cleanup.

### AA-4 — housekeeping (S, same session as landing)

Root import in `CsdLean4.lean`; audit pins in the **MathlibStaging** part
(`amplitude_amplification`, `amplitude_amplification_succeeds`, `ampStep_rotates`) with the
narrative comment carrying the standing disclaimer; glossary entry `amplitude-amplification`
(status `proved-in-corpus`, lean anchor, eponyms `[Brassard, Hoyer, Mosca, Tapp]`, backlink
header in the module; the Grover entry gains a `related` cross-link and its "provably nobody
will ever do better" BBBV prose stays untouched); ledger candidacy under the four criteria at
the next admission (terminal ✓ once AA-3 lands; claim-bearing via the outreach conversations;
pinned; distinct from any Grover row — there is none). Re-run the external priority check
(SQIR/Coq for *general* BHMT, not just Grover) before any public "first" sentence — CL-061's
rule.

### AA-5 — amplitude ESTIMATION (recorded, NOT committed; M–L, gate first)

The other half of the BHMT paper: estimating `a` itself by running phase estimation on `Q`,
whose eigenphases are `±2θ`. Now genuinely within reach **because `PhaseEstimation.lean`
exists** — and it would give the QFT/phase-estimation pair its second consumer, answering the
atlas assessment's sharpest number ("the QFT has exactly one consumer"). The work: `Q`'s
eigenvectors on the 2-plane (`e^{±2iθ}` eigenvalues — complex eigenvector algebra, cheap) +
instantiating `phase_estimation_lower_bound` at `φ = ±θ/π`-scaled phases + the estimate's
error propagation `|ã − a| ≤ 2π√(a(1−a))/T + π²/T²` (BHMT Thm 12 — the error algebra is the
real cost). **Gate:** scope the error-propagation arithmetic on paper first; if it exceeds a
session, land eigenvalues-only and record the rest. Do not open this brick before AA-1..4 are
merged.

**Gate run 2026-08-29 (after AA-1..4 merged), verdict: SPLIT.** The paper scoping decomposed
Thm 12 into four pieces: (i) `Q`'s eigenstructure on the plane — `g ± i·b` with `e^{±2iθ}`,
needs only linearity of the step, cheap; (ii) the error propagation — pure trig
(`sin²x − sin²y = sin(x+y)·sin(x−y)` + the Lipschitz bound on `sin`), cheap; (iii) the
two-register kickback state `(1/√T)Σₓ |x⟩ ⊗ Qˣψ` and its counting marginal — **requires
generalizing the Shor tensor infrastructure** (`tensorCN`/`qftInvCount` are hard-typed
`Fin T × ZMod N`; the second factor must become an arbitrary finite type). That generalization
is the SAME plumbing Shor's own deferred two-register marginal needs — a twofer, but M on its
own; (iv) the `8/π²` assembly — the branch decomposition has orthogonal eigenvector companions,
so the marginal is a half-half **mixture** of two single-phase distributions (no cross-terms,
unlike Shor's racing branches) and each branch gets the `4/π²` bound. (iii)+(iv) exceed the
session → per the gate, (i)+(ii) landed as **AA-5a** (executed same day, see below);
(iii)+(iv) are **AA-5b**, gated on the tensor generalization, first step the eigen-decomposition
of `ampState` (mechanical from `eigenPlus_add/sub_eigenMinus`, coefficients `(∓i/2)e^{±iγ}`,
branch weights `1/2` each).

### AA-6 — QSearch, unknown `a` (NOT planned; research-adjacent, author decision)

BHMT Thm 3's exponentially-growing randomized schedule (expected `O(1/√a)` with no knowledge
of `a`) needs expected-value analysis over the random iteration count — probability plumbing
of a different kind from anything above. Real, bounded, but a separate decision; nothing in
AA-1..5 depends on it. Recorded so it is not rediscovered as "missing".

## 4. Non-goals

* **No CSD claim.** The standing disclaimer in every docstring: the algorithm layer consumes
  the unitary pillar; witnesses mark scope. This module is library mathematics.
* **No repositioning.** The atlas assessment §4's guardrail: this lands in `Mathlib/`
  as Cat-1 and the repository's thesis lines do not change.
* **No gate-level circuits.** Operator level throughout, like the QFT ("matrix level only" —
  the same honest-scope sentence).
* **No "first" claims without the re-run priority check** (§3, AA-4).

## 5. Effort and sequencing

AA-1 **M**, AA-2 **S–M**, AA-3 **S–M** (with its abort valve), AA-4 **S**: one full session,
two if the coercion seams bite — the same shape as the phase-estimation extraction, which came
in on estimate. AA-5 is a second session behind its own gate; AA-6 is not scheduled.

Sequencing note: nothing here blocks or is blocked by the measurement-closure thread (D1's
residues are foundations/tooling, not algorithm work) or by C2/PBR. Per the atlas assessment,
this is a breadth play and knows it; the queue's research frontier (Q10 scoping) is untouched
by doing or not doing this.

## Execution record — 2026-08-29, same day as scoping

**AA-1..AA-4 EXECUTED.** `Mathlib/QuantumInfo/AmplitudeAmplification.lean` (475 lines, Cat-1):
★ `ampStep_ampState` (the two-reflection rotation), ★★ `amplitude_amplification` (the closed
form against `θ = arcsin √a`), ★ `amplitude_amplification_succeeds` (`⌊π/(4θ)⌋` rounds ⇒
success `≥ 1 − a` — closing the bound the old Grover file deferred), ★
`amplification_query_bound` (`m ≤ π/(4√a)`), `amplification_quarter` (the `a = 1/4`
single-round-certainty closed instance). Grover.lean rebuilt as the instance (404 → 335 lines):
`oracle_eq_oracleFlip`, `diffusion_eq_reflect` (a `rfl`!), `groverStep_eq_ampStep`,
`uniformState_eq_ampState`; `grover_success`/`grover_certain` re-derived with statements
unchanged (pins untouched); the `symState` parallel development deleted; ★
`grover_multi_success` (the `k`-marked instance) new. 6 MathlibStaging pins + 1 EmpiricalQM
pin; glossary entry `amplitude-amplification` (anchored, symmetric); full tree + audit parts
green.

**The priced-pilot number (the atlas assessment's ask):** the AA-3 refactor alone ≈ **25
minutes** wall-clock (two build-fix iterations); the whole general-module-plus-refactor session
≈ 90 minutes. At that rate "extract a mechanism, rebuild the instances on it" is S per
mechanism when the mathematics is already proved once — the atlas question is priced, and the
price is low.

**Snags worth carrying:** `rw [if_pos h]` rewrites every same-condition `ite` at once — dedupe
the rewrite list; an `ite` whose branches are real numerals in a ℂ-valued equation gets the
coercion wrapped OUTSIDE the `ite` (state branches as `(0 : ℂ)`/`↑(…)` explicitly); two `ite`s
on the same condition can carry different `Decidable` instances (`Finset.decidableMem` vs
`DecidableEq`-derived) making `if_pos/if_neg` miss — `simp only [Finset.mem_singleton]` +
`split_ifs` is the robust route; `rw [← Complex.ofReal_inv]` instantiates once per call, so two
distinct `(↑r)⁻¹` need two calls; higher-order `rw [Finset.sum_congr …]` under binders is
fragile — `norm_cast` + term-mode `sum_congr` instead.

AA-5 gate run and split 2026-08-29 (see the AA-5 section): **AA-5a EXECUTED same day** —
the eigenstructure (`ampStep` linearity, `eigenPlus/eigenMinus` with `e^{±2iθ}` eigenvalues,
the iterated eigen-action carrying the phase `e^{2ijθ}` a counting register would estimate)
and the error algebra (`sin²` product formula, the perturbation bound, and
`amplitude_estimation_error` — BHMT Lemma 7: angle error `ε` ⇒ amplitude error
`≤ 2√(a(1−a))·ε + ε²`), all in the same Cat-1 module, 3 new MathlibStaging pins. The AA-5a
slice took ≈50 minutes including build iterations (two `linear_combination`-coefficient rounds
on the `I² = −1` closings and one `conv_lhs`-rewrote-too-much restructure). **AA-5b** (the
kickback marginal + `8/π²` assembly) stays gated on the tensor generalization; AA-6 not
scheduled.

**AA-5b step 1 (the tensor generalization) EXECUTED 2026-08-29, same session.**
`Mathlib/QuantumInfo/JointRegister.lean` (Cat-1, ~260 lines): the product-index register over
arbitrary finite factors — `tensorState` (bilinear, basis law), `matrixLeft` (a matrix kernel
on the first factor; ★ `matrixLeft_tensorState`), `sliceLeft`, `probLeft` (the Born marginal;
product law), and the genuinely new ★★ `probLeft_sum_tensor_orthogonal`: a sum of product
states with pairwise-orthogonal second factors has a first-register marginal that is the
MIXTURE of branch marginals — every cross-term dead. ShorCore's `tensorCN`/`qftInvCount`/
`probCount` are now delegating instances (~90 lines of duplicate proof deleted; statements
unchanged, pins untouched; `qftInvCount_tensorCN` closes by cross-module `@[expose]` defeq
against `applyQFTinv`). 2 new MathlibStaging pins. What remains of AA-5b: the eigen
-decomposition of `ampState`, the kickback state `(1/√T)Σₓ |x⟩ ⊗ Qˣψ`, its marginal via the
mixture law, and the per-branch `4/π²` instantiation — one assembly session, no plumbing left.

One more snag for the pile: `push_cast` rewrites `↑(Real.sin x)` to `Complex.sin ↑x`
mid-goal, splitting what `linear_combination` needs to be ONE atom — prefer targeted
`Complex.ofReal_neg`-style simp lemmas over blanket `push_cast` when the closing is
`linear_combination` over mixed-cast trig atoms; and a simp set containing `ofReal_neg` will
break a later `exp_ofReal_mul_I` rewrite whose pattern needs the cast OUTSIDE the negation —
order the exp rewrite first.

## References

BHMT, *Quantum Amplitude Amplification and Estimation*, quant-ph/0005055 (Contemp. Math. 305,
2002); Nielsen–Chuang §6 (Grover), §5.2 (the phase-estimation half AA-5 would consume);
`CsdLean4/Empirical/QM/Algorithms/Grover.lean` (the instance and its deferred bound);
`CsdLean4/Mathlib/QuantumInfo/Register.lean` (the generalised R1 substrate),
`Fourier.lean` + `PhaseEstimation.lean` (the extracted pair, AA-5's consumers); vault:
`CSD - Algorithm Atlas Assessment 2026-08-21.md` (the pilot ask and the positioning
guardrails); `specs/nqubit-register-plan.md`; `specs/future-work.md`.
