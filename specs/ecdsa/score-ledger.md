# ECDSA.fail score ledger

> Moved from specs/active-todo.md 2026-07-19 — the ecdsa.fail track's score accounting. Code in `CsdLean4/Ecdsafail/`.


**HARNESS FINDINGS 2026-07-16 (from github.com/jieyilong/ecdsafail-autoresearch-harness, benhuang2025 —
a real leaderboard participant's tooling; see [[reference_ecdsafail_harness]]).** Material for the honesty
framing of this ledger:
- **The scored metric is `score = peak_qubits × AVERAGE EXECUTED Toffoli`** (NOT worst-case emitted).
  Frontier: peak = 1156 qubits, avgT ≈ 1,365,020 → score ≈ 1.577×10⁹ (matches our `ecdsaFailLeaderboardBest
  = 1.57×10⁹`). Our corpus counts WORST-CASE UPPER-BOUND EMITTED Toffoli on a FULL-WIDTH VALUE-EXACT
  circuit; the leaderboard scores AVERAGE-EXECUTED Toffoli on a TRUNCATED circuit (correct on most inputs,
  hard inputs dodged by nonce-hunting). These are DIFFERENT QUANTITIES — our figures are honestly higher by
  construction, and the "~Nx off leaderboard" lines below conflate the two axes. Keep the two-track posture.
- **Their central rule: "certify value-exactness STATICALLY, never by sampling"** (a control firing 1/1e6
  passes 1e6 shots yet breaks the circuit). Our Lean proofs ARE the machine-checked gold-standard form of
  exactly that methodology — the #36c divstep verification is the rigorous version of what they do with
  def-use liveness / algebraic identity / constprop. Strong validation of the formal-verification approach.
- **Generalizable negatives (save effort):** (i) `jump=4` (wider-jump GCD rewrite) is REFUTED — structurally
  +32–67% MORE Toffoli, cost inherent (controlled-shift cswaps); our safegcd `jump=2`-equiv is right, don't
  pursue wider jumps. (ii) A CCX folds cheaper ONLY when inputs are affine-related (equal / complementary /
  constant) — no sound fourth relation. (iii) **GCD lane-0 cswap elision** (`divstep 0..n → 1..n`): the
  bit-0 conditional swap is a no-op — a real frontier Toffoli lever, potentially a verifiable lemma for
  `condSwapReg` (start the swap ladder at index 1). (iv) Truncation trades score for hard inputs (the λ
  cliff) — an input-dependent optimisation OUTSIDE the value-exact regime our verification certifies.

**THREE-TRACK SCORE LEDGER 2026-07-17 (ThreeTrackScore.lean + SafegcdExecCost.lean).** The point-add SCORE
(peak×Toffoli) split three ways: **Verified** = verifiedFloor 676,880,936 × peak 2822 = 1.91×10¹²;
**Trusted** = trustedEstimate 7,801,612 × peak 2822 = 2.20×10¹⁰; **Leaderboard** (competition convention) =
optimised peak 1156 × **CALCULATED** avg-executed 1,950,403 = **2,254,665,868 ≈ 2.25×10⁹ — ~1.44× the live
best** (`leaderboard_calculated_gap`). The avg-executed is COMPUTED, not adopted: `SafegcdExecCost.lean`
implements the competition's executed-Toffoli rule (`executedToffoli`: CCX counts iff both controls set)
and MEASURES it on the verified n=3 adder over all 2^7 inputs = **25% executed/emitted** (192/(128·6));
× emitted worst-case 7,801,612 = 1,950,403. Honest tier: a grounded MODEL (single gadget, uniform inputs,
pre-constprop), in the frontier's ballpark (~1.37×10⁶) but NOT a win (`leaderboard_not_below_best`: above
best; residual = constprop + peak-reduction we have not applied). Exact figure needs the assembled op-stream
+ eval_circuit (#7). The defensible headline remains the machine-checked value-exactness (#36c).

**TWO-TRACK REFRAME 2026-07-01 (TwoTrack.lean, specs/ecdsa/ecdsafail-two-track.md, auditor-SOUND):** the
figures below split by TRUST BASIS. The honest **VERIFIED FLOOR** is `secp256k1Toffoli_verifiedFloor =
676,880,936` (Fermat inversion — the ONLY inverter the corpus can machine-anchor, verified multiply +
anchored O(n³) Fermat with the PROVEN op-count `fermatInvFieldMults_le`). The `5,831,948` "best" is the
**TRUSTED ESTIMATE** (`secp256k1Toffoli_trustedEstimate`, safegcd + Karatsuba + squaring — cited to
Bernstein-Yang/RNSL/Karatsuba-Ofman, NOT Lean-verified, NOT a corpus achievement). Gap ~116× = the
VERIFICATION FRONTIER (verifying those primitives, esp. the safegcd divstep circuit, collapses it). So
the "~10.5× off leaderboard" line below judged a VERIFIER on the ESTIMATORS' axis; the honest posture is
verified-floor + cited trusted-estimate + the named frontier between them.

| stage (trust basis) | Toffoli | score | leaderboard gap |
|---|---|---|---|
| **VERIFIED FLOOR** (Fermat, verified+anchored) | 676,880,936 | 1,910,158,001,392 | ~1217× |
| + L6 safegcd (→ trusted) | 7,896,616 | 22,284,250,352 | ~14× |
| + L1 Karatsuba (trusted) | 5,913,868 | 16,688,935,496 | ~10.6× |
| **TRUSTED ESTIMATE** (+ L3 squaring) | 5,831,948 | 16,457,757,256 | ~10.5× |
| leaderboard best (trusted, external) | ~1,360,000 | ~1,566,720,000 | 1× |

Per-field-op constant levers (L6/L1/L3) exhausted. Current ~5.83M Toffoli/point-add is
**inversion-dominated**: safegcd `60n²+28n` ≈ 3.94M at n=256 (~67%); mults/squarings/adds the
rest. Standalone adders are an O(n) sliver of an O(n²) total — which is why the L5-d adder
re-cost barely moves the score.

**HONESTY CORRECTION (2026-06-30): L5-d as built is NOT a score lever.** The #30 AND-based
adder is `6n` Toffoli (`andCarryCell` = 3 CCX/carry, fresh-ancilla majority cell), ~3× a
Cuccaro adder (~2n ≈ 512 at n=256). After the measurement re-cost it is `3n` = 768, STILL
larger than Cuccaro's ~2n. So swapping #30 into the point-addition RAISES the score. #30/#21
are the measurement-path proof-of-concept (the `andInput`-shaped uncompute attachment point),
not a competitive adder.

**UPDATE 2026-06-30: the minimal adder is now BUILT (#35, GidneyAdder.lean).** `gidneyAdd` is
value-correct general-n (`gidneyAdd_correct`), `2n` Toffoli unitary (ties Cuccaro), `n` via the
measurement re-cost (`gidney_beats_cuccaro`: n < Cuccaro 2n < #30 6n; n=256: 256/512/1536),
foundational-triple, auditor-SOUND. So Tier-X step (i) is done. The score lever now reduces to
step (ii) — **#36: thread the Gidney/carry-clean adder pervasively through the O(n²)
multiplier/inverter** (`ModularMulLoop`/`SafegcdInversion`), where the inversion-dominated 5.83M
lives (a single adder swap barely moves it) — plus step #7 (user harness). The "gap → ~5×" target
is now gated on #36, not on an unbuilt adder.

