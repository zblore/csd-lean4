# ECDSA.fail optimization plan — toward the best VERIFIED optimised point-addition score

**Status: planned (2026-06-28).** Supersedes the "worst-case upper bound" posture of step 3.
Goal restated by the user: **aim for the best verified *optimised* result, not the worst verified
result.** This file inventories the levers, tiers each by whether it is expressible in the current
verified measurement-free CCX DSL, estimates impact, and sequences the work. Companion:
`specs/ecdsafail-correlation.md` (the object-correlation guard; step 2 reproduction is the user's
machine action and gates any claim of a validated comparison).

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

Estimated Tier-V-only outcome: L1×L2×L3 ≈ a `3–5× · 2–4× · ~1.3×` ≈ **~10–25× Toffoli reduction**,
landing the score in the low **10^10–10^11** range — a large improvement over 1.9×10^12, but still
~10–60× off the leaderboard's 1.57×10^9. **Verified CCX-only cannot reach parity** (see Tier X).

### Tier X — needs a DSL extension (architecture decision required)

- **L5. Measurement-based (Gidney) adders — the single biggest remaining lever.** The leaderboard
  (and all of Litinski/Babbush/Schrottenloher) use measurement-based uncomputation: ~**1 Toffoli/bit**
  vs our 2, i.e. a flat ~2× on *every* adder, hence ~2× on the whole figure, and it is the technique
  that makes their full addition cost ~1 modmul. **It is inexpressible in the current measurement-free
  CCX DSL.** Capturing it requires extending `Reversible/Circuit.lean` with a measurement gate +
  classically-controlled correction, and giving it honest denotational semantics (probabilistic /
  deferred-measurement). This is a verification-careful sub-project: done naively (cost-only, no real
  semantics) it would be exactly the "hollow cost" the programme rejected. **Fork point for the user.**
- **L6. Bernstein–Yang safegcd inversion (alternative to L1×L2 on the inversion).** A constant-time
  binary-GCD inversion is dominated by additions/shifts/conditional-swaps, not multiplications, and can
  be dramatically cheaper than even an optimized Fermat exponentiation. But the reversible safegcd
  circuit + its correctness proof (the GCD invariant over `n` iterations) is a large new build,
  independent of the multiply stack. Highest ceiling on sub-lever (B); highest build cost.

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
3. **L1 (Karatsuba) — the big verified-now lever.** Reused by every modmul and the inversion. Largest
   verified-CCX score improvement. Re-cost the benchmark after.
4. **L2 (windowed Fermat) — fewer modmuls.** Compose with L1; re-cost.
5. **Reassess vs the harness (after step 2):** report the best verified-CCX score and its gap to the
   leaderboard. Decide the **fork**: stop at best-verified-CCX, or invest in Tier X.
6. **Tier X (user-gated):** L5 (measurement-based-adder DSL extension, ~2× everywhere) and/or
   L6 (safegcd inversion). These are the only paths to leaderboard parity and each is a large,
   verification-careful tranche.

## Honest target

- **Best verified CCX-only (Tier V):** realistically ~10–25× better than step 3, i.e. score
  ~10^10–10^11 — a credible "best verified result *in a measurement-free reversible model*", with the
  gap to the leaderboard fully attributed to the absent measurement-based adders (L5).
- **Leaderboard parity:** requires Tier X (L5 + L6) — a measurement-gate DSL with honest semantics
  plus a verified safegcd inversion. Achievable in principle, but it is a multi-tranche commitment and
  changes the DSL's trust story; the user should opt in explicitly before we start it.

The standing rule holds: do not claim any optimised number as an ECDSA.fail result until step 2
validates the object comparison and each lever's circuit is verified (`⟦c⟧ = op`), not cost-only.
