# Two-track ECDSA resource accounting: verified floor, trusted estimate, frontier

Status: DONE 2026-07-01. Reporting layer only (no circuit re-derived).
Lean: `CsdLean4/Mathlib/QuantumInfo/ECDLP/TwoTrack.lean` +
`CsdLean4/Mathlib/QuantumInfo/ECDLP/TrustedEstimate.lean` (Stage-1 trusted leaderboard estimate).
Pins: `CsdLean4/Tests/AxiomAudit.lean` (seven TwoTrack pins + fourteen TrustedEstimate pins,
foundational-triple plus propext, no busch).

## Purpose

Make the trust basis of every quoted secp256k1 cost figure explicit, and report two numbers side by
side instead of one: a verified floor built only from machine-verified and value-correct/anchored
primitives, and a trusted estimate built from the decades-audited textbook primitives cited to the
literature. The delta between them is named the verification frontier: the roadmap.

## Verifier versus estimator posture

The public ECDLP resource leaderboards are resource ESTIMATORS. They compose trusted textbook primitives
and validate by small-instance simulation plus peer review, not by machine proof. This corpus VERIFIES
the arithmetic at denote level (a reversible circuit whose denotation is proved equal to the intended
value), a different and harder standard. Judging a verifier on the estimators' single-number axis
produces the misleading headline "N times off the leaderboard". The honest report is three objects: a
verified floor, a trusted reference estimate, and the named frontier between them.

The trusted-track figures are literature-cited references, NOT corpus achievements. The corpus has not
verified the safegcd divstep circuit, the Karatsuba circuit, or measurement-based arithmetic as
reversible circuits.

## The trust ladder

- verified: machine-checked denote-level circuit correctness. Reference: the carry-clean modular
  multiply `cleanModMulToffoli n = 20*n^2 + 14*n`, tied to `Reversible.cuccaroModMul` by
  `cleanModMulToffoli_eq_cuccaro`, value `Reversible.cuccaroModMul_correct`. Reference adder:
  `Reversible.cuccaroModAdd_toffoli = 12*n + 10`.
- anchored: value-correct in ZMod with verified sub-primitives, but a documented op-count model for the
  control flow. Reference: the Fermat inversion `fermatInvToffoli n = (2*n) * cleanModMulToffoli n`.
  Value `ECDLP.fermatInv_eq_inv` proved (primality load-bearing); each field multiply verified; the
  `2*n` square-and-multiply exponent schedule a documented model, no exhibited exponentiation circuit.
- trusted: a decades-audited construction accepted from the literature without a Lean circuit proof,
  cited to source. In this corpus: safegcd / Bernstein-Yang GCD-inverse; Gidney measurement
  uncomputation; the Karatsuba sub-quadratic multiply recurrence; windowed elliptic-curve recoding.

## The two figures (secp256k1, one affine point addition, classical offset)

| track | figure | Toffoli | composition | basis |
| --- | --- | --- | --- | --- |
| verified floor | `secp256k1Toffoli_verifiedFloor` | 676880936 | 3 carry-clean multiplies + Fermat inversion + classical-offset adders | verified + anchored only |
| trusted estimate | `secp256k1Toffoli_trustedEstimate` | 5831948 | 2 Karatsuba multiplies + 1 dedicated squaring + safegcd inversion | trusted primitives |

The verified floor is the LARGER number. The only inversion the corpus can machine-anchor is the Fermat
exponentiation, which is order n cubed and dominates the point addition. The trusted estimate replaces it
with the order n squared safegcd inversion and the sub-quadratic Karatsuba multiply.

Load-bearing honesty check (`verifiedFloor_no_trusted_leak`): every component of the verified floor tags
as verified or anchored, none as trusted. And (`trustedEstimate_uses_trusted`) the trusted estimate's
distinguishing inputs (safegcd, Karatsuba, squaring) each tag as trusted.

## The gap

`two_track_gap_lower`: `trustedEstimate * 116 < verifiedFloor` (5831948 * 116 = 676505968 < 676880936).
`two_track_gap_upper`: `verifiedFloor < trustedEstimate * 117` (676880936 < 682337916).

The gap is a factor of about 116. That factor IS the verification frontier: it is exactly what verifying
safegcd, Karatsuba, and measurement-based arithmetic as reversible circuits would buy. The gap is the
roadmap, not a deficiency of the verified floor.

## The verification frontier (roadmap; `verificationFrontier`, four entries)

1. safegcd divstep circuit: a reversible Bernstein-Yang / Roetteler-Naehrig-Svore-Lauter divstep
   recurrence whose denotation is the modular inverse, with a proved GCD/Bezout invariant and
   termination. Currently the corpus value is a definitional unfolding of `ZMod.inv`
   (`binGcdInv_eq_inv`) and the 2n divstep count is a documented op-count model.
2. measurement-based adder and multiply: Gidney measurement uncomputation at one Toffoli per bit. Not
   expressible in the measurement-free CCX DSL; the `gidneyMeasAddToffoli` handle costs only the
   measurement half (equals n).
3. sub-quadratic multiply circuit: a divide-and-conquer Karatsuba reversible circuit whose denotation is
   X times Y mod N with the split and recombine proved. Currently the value rides on the verified
   schoolbook `cuccaroModMul_correct` and the 3-way recurrence shape is documented (`karatsuba_identity`
   is the algebra, not a circuit).
4. windowed elliptic-curve scalar recoding: precomputed tables of 2^i times P cutting additions.
   Currently an op-count model, not a verified windowed circuit.

## Citations (trusted track; not verified in this corpus)

- Roetteler, Naehrig, Svore, Lauter, "Quantum resource estimates for computing elliptic curve discrete
  logarithms", ASIACRYPT 2017 (eprint 2017/598). Reversible GCD-inverse baseline.
- Bernstein, Yang, "Fast constant-time gcd computation and modular inversion", CHES 2019. The safegcd
  divstep inversion.
- Gidney, "Halving the cost of quantum addition", Quantum 2 (2018) 74. Measurement-based uncomputation.
- Litinski, "How to compute a 256-bit elliptic curve private key with only 50 million Toffoli gates",
  arXiv 2306.08585 (2023). Aggressively-optimised end of the estimator range (the ~4.5n qubit layout).
- Haener, Jaques, Naehrig, Roetteler, Soeken, "Improved quantum circuits for elliptic curve discrete
  logarithms", PQCrypto 2020 (eprint 2020/077). Windowed EC.
- Karatsuba, Ofman, "Multiplication of many-digital numbers by automatic computers", 1962. Sub-quadratic
  multiply.

## Stage-1 trusted leaderboard estimate (`TrustedEstimate.lean`)

Purpose: push the trusted estimate down toward the ecdsa.fail leaderboard band by REPRODUCING the leaders'
cited primitives on top of `secp256k1Toffoli_trustedEstimate = 5831948` (safegcd + Karatsuba + squaring),
add a trusted peak-qubit model, and compose the trusted SCORE (peak-qubits times Toffoli, the leaderboard
metric). Reporting layer only; no circuit built or verified. Every figure is `trusted` (cited, not
Lean-verified). The verified floor and the anchored figures of `TwoTrack.lean` / `PointAddBenchmark.lean`
are untouched.

CRITICAL HONESTY: the trusted route REPRODUCES the leaders' primitives as a cited reference; it does NOT
beat them (beating needs a novel construction = research). Reaching number one exactly means reproducing
the number-one construction. NO figure here is verified or a corpus achievement; the distinctive corpus
result is the VERIFIED entry (denote-level circuit correctness), not the trusted rank. A Lean cost figure
is not a leaderboard submission: that needs the ecdsa.fail harness run on the identical operation (the
user's step 7).

### The two cited reduction primitives (trusted, not verified here)

- Gidney measurement-based uncomputation, factor 2. X-basis measurement + CZ correction removes the
  reverse-pass Toffolis of the AND-heavy arithmetic (multiply, squaring, safegcd divstep adders), roughly
  halving the Toffoli. Adder witness in the corpus: `CSD.Empirical.QM.gidneyMeasAddToffoli = n`, exactly
  half Cuccaro `2n`. Cited: Gidney, "Halving the cost of quantum addition", Quantum 2 (2018) 74. The
  measurement-discipline circuit is not expressible in the corpus CCX DSL and is not verified here.
- Windowed elliptic-curve recoding, factor 2. Windowed scalar recoding + projective coordinates amortise
  the per-addition schedule; the leaderboard's per-point-operation figure is windowed-amortised, not a
  naive standalone affine addition. Applied as a documented window factor 2. Cited: Roetteler-Naehrig-
  Svore-Lauter 2017 (eprint 2017/598), Haener-Jaques-Naehrig-Roetteler-Soeken 2020 (eprint 2020/077). The
  windowed circuit is not verified here.

### The trusted figures (secp256k1, all trusted, all cited)

| figure | value | composition | basis |
| --- | --- | --- | --- |
| `secp256k1Toffoli_measGidney` | 2915974 | trusted estimate with Gidney factor 2 | trusted |
| `secp256k1Toffoli_trustedEstimate_v2` | 1457987 | Gidney factor 2 then windowing factor 2 (= /4) | trusted |
| `secp256k1Qubits_trustedEstimate` | 2304 | 9n documented layout (2n coords + 3n working + 3n meas-clean scratch + n window table) | trusted |
| `secp256k1Score_trustedEstimate` | 3359202048 | qubits times Toffoli (the ecdsa.fail metric) | trusted |

The qubit model is anchored to `onePointAddPeakQubits = 11n+6 = 2822`: the `cleanModMulQubits = 6n+6`
scratch bank is roughly halved by Gidney measurement-clean ancilla management (to 3n), and a windowed-table
register n is added, netting 9n = 2304. This is the Roetteler-2017 / Haener-2020 windowed-projective range
(cited counts about 2100 to 2330), NOT the aggressive Litinski-2023 / Babbush measurement-based
ancilla-recycling layout (about 4.5n, about 1152) of the number-one entry.

Honesty check (`trustedEstimate_v2_uses_trusted`, decide): every new figure tags `trusted` (cited, not
verified). No verified or anchored figure is touched.

### The leaderboard comparison (honest rank, from the arithmetic)

Leaderboard best (late June 2026, corpus-recorded): about 1152 peak qubits times about 1360000 Toffoli,
exact product `leaderboardScoreExact = 1566720000` (corpus rounded handle `ecdsaFailLeaderboardBest =
1570000000`).

- Toffoli, essentially reproduced: `1360000 < secp256k1Toffoli_trustedEstimate_v2 = 1457987` and within
  about 1.08 times (`toffoli_v2_reproduces_leaderboard`: `v2 * 100 < leaderboardToffoli * 108`). Same
  cited primitives, so REPRODUCES the leaders' Toffoli band, slightly above; does not beat it.
- Qubits, a factor of two above: `secp256k1Qubits_trustedEstimate = 2 * leaderboardQubits` (2304 = 2*1152,
  `qubits_trustedEstimate_two_leaderboard`). This is the whole score residual.
- Score, about 2.14 times number one: `leaderboardScoreExact * 2 < secp256k1Score_trustedEstimate <
  leaderboardScoreExact * 3` (3133440000 < 3359202048 < 4700160000,
  `score_trustedEstimate_vs_leaderboard_lower` / `_upper`; and the same brackets against the rounded handle
  in `score_trustedEstimate_vs_rounded_leaderboard`).

Honest rank: the trusted score does NOT reach number one. It lands at about 2.14 times the number-one
score, with the Toffoli reproducing the leaders' band (about 1.07 times) and the ENTIRE residual in the
peak-qubit count (exactly 2 times). The primitive that would close it is the aggressive measurement-based
AND-ancilla-recycling qubit layout of Litinski 2023 / Babbush et al. (about 4.5n peak qubits, about 1152),
named and cited, NOT modelled here because modelling it is reproducing the number-one construction, not a
bounded re-cost. The corpus records only the number-one leaderboard figure, so no specific top-N rank is
claimed beyond the number-one comparison the arithmetic supports.

### Standing caveats

- Reproduces, not beats: the trusted route uses the leaders' own primitives; a genuine improvement needs a
  novel construction (research), not a re-cost.
- A Lean cost figure is not a leaderboard submission. The ecdsa.fail leaderboard scores a RUST-CODED
  reversible circuit for one secp256k1 point addition, by the peak-qubit times Toffoli product, run through
  their harness (confirmed 2026-07-01 against ecdsa.fail + the ecdsafail-challenge repo). So getting on the
  board requires WRITING the competitive Rust circuit and running the harness, not just a Lean number.
  This Stage-1 estimate is a TARGET SPEC (what number a good construction should hit), not a submission.
- The leaderboard does NOT accept Lean proofs either: its harness scores Rust circuits, so a "verified
  entry on ecdsa.fail" is not a category the board has. The distinctive corpus result (the VERIFIED
  floor, denote-level circuit correctness) is a first-of-kind artifact on its OWN axis (a formally
  verified quantum resource bound, publishable as a paper/repo headline), NOT an ecdsa.fail entry.

### Citations added for Stage-1 (trusted; not verified here)

- Litinski, "How to compute a 256-bit elliptic curve private key with only 50 million Toffoli gates",
  arXiv 2306.08585 (2023). Aggressive measurement-based ancilla-recycling layout (the about-4.5n qubit
  end that the number-one entry uses).
- Babbush et al. (Google), reduced-gate/reduced-qubit ECDLP estimates. The aggressive qubit-layout end
  cited for the residual to number one.
