# ECDSA.fail optimization plan — toward the best VERIFIED optimised point-addition score

**Status: L6 DONE 2026-06-28 (the dominant lever); L1/L2/L3/L5 pending.** Supersedes the "worst-case
upper bound" posture of step 3. Goal restated by the user: **aim for the best verified *optimised*
result, not the worst verified result.** This file inventories the levers, tiers each by whether it is
expressible in the current verified measurement-free CCX DSL, estimates impact, and sequences the work.
Companion: `specs/ecdsafail-correlation.md` (the object-correlation guard; step 2 reproduction is the
user's machine action and gates any claim of a validated comparison).

**L6 result (`ECDLP/SafegcdInversion.lean`, auditor-SOUND).** The binary-GCD / safegcd inversion
replaced Fermat: per-inversion Toffoli `672,923,648 → 3,939,328` (~170×), `onePointAddToffoli
676,880,936 → 7,896,616`, **`onePointAddScore 1,910,158,001,392 → 22,284,250,352` (~86×)**, closing the
leaderboard gap **~1217× → ~14×**. The dominant ~86× of the ~1220× gap is eliminated; the residual ~14×
is now the multiply term + windowing + measurement adders + the worst-case-vs-executed modelling gap, no
longer the inversion. HONESTY (auditor-corrected): `binGcdInv` is DEFINITIONALLY Mathlib's `ZMod.inv`
(xgcd-based), so `binGcdInv_eq_inv` is an unfolding, not an independent algorithm-correctness proof
(weaker than `fermatInv_eq_inv`, which is a genuine theorem); the real coprimality-load-bearing value
export is `binGcdInv_mul_eq_one : a * binGcdInv N a = 1`. Cost = derived op-count model tied to verified
gadgets (`divstepToffoli = modSub + cuccaroCModAdd + cuccaroModDouble`), DOCUMENTED divstep count `2n`,
and an honestly-flagged lower-fidelity proxy (single Bézout track + doubling-for-halving, so the win is
if anything optimistic on the safegcd side). Full per-divstep bit-circuit (route 2a) deferred.

## Where we stand (the gap)

The benchmark scores ONE secp256k1 point addition on the **qubit × Toffoli product, lower wins**.

| | Peak qubits | Toffoli | Score (product) | vs best |
|---|---|---|---|---|
| Ours (`PointAddBenchmark`, step 3) | 2,822 | 676,880,936 | 1,910,158,001,392 | ~1,220× worse |
| Leaderboard best (late June 2026) | ~1,152 | ~1,360,000 | ~1,566,720,000 | 1× |

Literature ladder (for calibration): Litinski 2023 → Babbush et al. (Google) 2–3× fewer gates AND
qubits → Schrottenloher (arXiv 2606.02235 / eprint 2026/1128) reverse-engineered Babbush, ~1.5%
more qubits and 6.5–10% fewer Toffolis, **circuit disclosed**. The leaderboard is ~47% ahead of
Google's published benchmark on the product metric.

**Diagnosis — the entire Toffoli gap is one component.** Our qubit count (2,822) is already within
~2.4× of the best — same order of magnitude. The killer is Toffolis, and it is traceable to a single
choice: we cost the field inversion by **Fermat's little theorem** (`a^(p−2)` = `2n = 512` modular
multiplies → `fermatInvToffoli 256 = 672,923,648`, **99.4%** of our total), and each of our modular
multiplies is the **schoolbook carry-clean `cleanModMulToffoli 256 ≈ 1.31 million`**. The leaderboard
performs an entire point addition — inversion included — in ~1.36M Toffolis, i.e. about **one** of our
modular multiplies. So the gap decomposes as:

```
our 677M  =  ~515 modmul-equivalents  (3 mults + 512 for Fermat inversion)
their 1.36M ≈   1 modmul-equivalent
```

The two independent sub-levers: **(A) make each modmul much cheaper**, and **(B) do far fewer
modmul-equivalents** (cheaper inversion). Both are needed.

## Lever inventory (tiered by DSL-expressibility)

### Tier V — verified NOW (expressible in the current CCX DSL, no architecture change)

- **L1. Karatsuba modular multiplication.** Replace the `O(n²)` schoolbook multiply with Karatsuba
  recursion (`O(n^1.585)`). At n=256 that is roughly a `256² / 256^1.585 ≈ 6×` reduction in
  partial-product work (less after recursion overhead and the extra additions; realistic ~3–5× per
  modmul). Because the Fermat inversion is 512 modmuls, this propagates ~3–5× through the *whole*
  figure. **Highest-leverage verified-now lever** (touches every field multiply). Build: a recursive
  `karatsubaMul` circuit + correctness over `regVal`/`ZMod`, reusing the Cuccaro adders; cost lemma
  `karatsubaToffoli n`. Substantial but self-contained.
- **L2. Windowed modular exponentiation for the inversion.** The Fermat inversion is fixed-exponent
  `a^(p−2)`; `2^k`-ary windowing (precompute `a^1..a^(2^k−1)`, square-and-multiply by window) cuts the
  number of multiplications from `~2n` toward `~n/k · (1 + 1/?)`. With the exponent classical (p is a
  constant) the window schedule is classical — no quantum table needed. Realistic ~2–4× fewer
  modmuls. Build: a windowed `modExp` schedule + cost; correctness reuses `mulLoop`.
- **L3. Optimized squaring / shared partial products.** `M_dbl = 8` / `M_add = 17` sit one above the
  EFD optima (`2M+5S=7`, `11M+5S=16`) because squarings are recomputed, not folded via the
  `(a+b)²` / `(X+YY)²` tricks. A dedicated `sqr` circuit (`~n²/2` partial products vs `n²`) plus
  sharing closes the M-count gap and halves squaring cost. Modest but cheap; composes with L1.
- **L4. Carry-clean adders — DONE.** `CuccaroAdd`/`CuccaroModAdd`/`CuccaroModMul` already capture the
  Θ(n)-qubit, 2-Toffoli/bit adder (the ~1.5× win + the qubit collapse to ~6n). No further verified-now
  win here without L5.

- **L6. Bernstein–Yang safegcd / Kaliski binary-GCD inversion — THE dominant lever, verified-now.**
  A constant-time binary-GCD inversion is dominated by additions/shifts/conditional-swaps, NOT
  multiplications — all expressible in the current Boolean CCX DSL, **no measurement, no DSL
  extension**. Safegcd inversion costs roughly a handful of multiplies' worth of work versus Fermat's
  `2n = 512` multiplications, so it plausibly cuts the inversion (which is **99.4%** of our Toffolis)
  by ~25–100×. This is the single most important lever and it is fully verifiable today. Cost: a large
  new build (a reversible divstep circuit + the GCD invariant over `n` divsteps; a known reversible
  algorithm in the ECDLP literature, but a substantial correctness proof). Replaces, rather than
  composes with, L1×L2 on the inversion.

Estimated verified-CCX outcome (L6 dominant + L1 on the residual multiplies + L3): the inversion
collapses from `~512` to `~10–20` modmul-equivalents, and each of those is Karatsuba-cheaper, plausibly
landing the score **within ~2–5× of the leaderboard, all verified in the current DSL**. The earlier
claim "verified CCX-only cannot reach parity" was wrong — it assumed Fermat inversion was fixed; with
safegcd, CCX-only gets *most* of the way to parity. Only the last ~2× (below) needs more.

### Tier X — verifiable, but needs amplitude-level measurement semantics (the only true extension)

- **L5. Measurement-based (Gidney) adders — the last ~2×.** The leaderboard (and
  Litinski/Babbush/Schrottenloher) use measurement-based uncomputation: ~**1 Toffoli/bit** vs our 2, a
  flat ~2× on every adder. Gidney's trick measures an ancilla in the **X-basis** and applies a **CZ**
  correction — it fundamentally uses *phases*, so it is **not** expressible in the Boolean-state
  reversible DSL (`denote : (Fin n → Bool) → …`), which has no amplitudes. **It IS verifiable in Lean**,
  just at a deeper layer: the proof obligation is that the measure+correct gadget's *net channel* =
  (identity on the data register) ⊗ (ancilla reset), for every measurement outcome. The corpus's
  **QuantumInfo branch already has the primitives** (projective measurement, Clifford gates, CPTP
  `Channel`s, `PartialTrace`), so this is a legitimate verified theorem, **not** a cost-only / "hollow"
  shortcut. The real costs are (a) bridging the Boolean arithmetic circuits into the amplitude model and
  (b) a larger trusted semantic base. **This is the user-gated fork** — not "verify vs. don't", but "how
  much amplitude-semantics investment for the final ~2×".

### Tier E — external / out of scope for the single-addition object

- **L7. Windowing / lookup-table point addition.** The full ECDLP attack amortizes inversion across
  many additions via windowed lookups; this does **not** apply to the benchmark's *standalone single*
  addition (affine in/out, classical offset), so it cannot lower the single-addition score. Noted to
  prevent a category error.

## The product metric (don't optimize Toffoli in isolation)

The score is qubit × Toffoli. We are Toffoli-bound (~500×) and qubit-light (~2.4×), so Toffoli
reduction dominates — but L1 (Karatsuba) and L6 (safegcd) *add ancilla*, so each lever must be scored
on the **product**, not Toffoli alone. Track `peakQubits` alongside `Toffoli` at every step; a 4×
Toffoli win that doubles qubits is only a 2× score win.

## Sequenced plan

1. **Step 2 (USER, blocking the *comparison*):** run the ECDSA.fail Rust harness on the identical
   one-addition op (`! cargo run --release …` in a checkout of their repo); record
   `toffoli / clifford / peak qubits / score / correct`. Until then our score is a comparable-OBJECT
   figure, not a validated comparison, and we cannot know which lever the *executed-average* metric
   actually rewards.
2. **L3 (squaring) — warm-up, cheap.** Closes the M-count gap; small standalone win; exercises the
   sqr-circuit pattern L1 will reuse.
3. **L6 (safegcd inversion) — THE dominant verified-now lever.** Replaces Fermat (99.4% of our cost)
   with a reversible binary-GCD inversion, no measurement, current DSL. Largest single score
   improvement; the centerpiece. Large build (reversible divstep + GCD invariant). Re-cost after.
4. **L1 (Karatsuba) — cheaper residual multiplies.** Reused by the few multiplies safegcd and the
   addition formula still need. Re-cost.
5. **Reassess vs the harness (after step 2):** report the best verified-CCX score and its gap (expected
   within ~2–5×). Decide the **fork**: stop at best-verified-CCX, or invest in Tier X for the last ~2×.
6. **Tier X (user-gated):** L5 (Gidney measurement adders) verified via the QuantumInfo amplitude
   semantics — the only path to the final ~2× / full parity, a deeper multi-tranche commitment.

## Honest target

- **Best verified, current Boolean DSL (Tier V, incl. L6 safegcd):** the dominant lever (safegcd
  inversion, no measurement) plus Karatsuba/squaring plausibly land the score **within ~2–5× of the
  leaderboard, fully verified in Lean today** — no DSL extension. This is the main prize and it is
  entirely within the current trust story.
- **Leaderboard parity (Tier X, L5):** the final ~2× from Gidney measurement-based adders. Still
  verifiable in Lean, but via the QuantumInfo amplitude/measurement/CPTP machinery (prove the
  measure+correct gadget = identity-on-data ⊗ ancilla-reset for all outcomes), which means bridging the
  arithmetic circuits into the amplitude model and accepting a larger trusted semantic base. A
  multi-tranche commitment; the user should opt in explicitly. NOT cost-only — a genuine verified
  theorem, just deeper.

**Correction to the earlier framing:** "best verified in Lean" can pursue leaderboard parity essentially
all the way. The 99.4%-of-cost lever (safegcd inversion) needs no measurement and no DSL change; only the
last ~2× needs amplitude-level measurement semantics, which the QuantumInfo branch supports. Nothing on
this path is intrinsically unverifiable or cost-only.

The standing rule holds: do not claim any optimised number as an ECDSA.fail result until step 2
validates the object comparison and each lever's circuit is verified (`⟦c⟧ = op`), not cost-only.
