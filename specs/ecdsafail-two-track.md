# Two-track ECDSA resource accounting: verified floor, trusted estimate, frontier

Status: DONE 2026-07-01. Reporting layer only (no circuit re-derived).
Lean: `CsdLean4/Mathlib/QuantumInfo/ECDLP/TwoTrack.lean`.
Pins: `CsdLean4/Tests/AxiomAudit.lean` (seven pins, foundational-triple plus propext, no busch).

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
- Gidney, "How to factor 2048 bit RSA integers in 8 hours ... 50 million Toffoli" line, arXiv 2306.08585
  (2023). Aggressively-optimised end of the estimator range.
- Haener, Jaques, Naehrig, Roetteler, Soeken, "Improved quantum circuits for elliptic curve discrete
  logarithms", PQCrypto 2020 (eprint 2020/077). Windowed EC.
- Karatsuba, Ofman, "Multiplication of many-digital numbers by automatic computers", 1962. Sub-quadratic
  multiply.
