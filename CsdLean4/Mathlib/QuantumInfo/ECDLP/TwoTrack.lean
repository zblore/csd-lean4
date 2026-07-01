import CsdLean4.Mathlib.QuantumInfo.ECDLP.KaratsubaMul

/-!
# Two-track ECDSA resource accounting: verified floor, trusted estimate, and the frontier

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This is a **reporting layer** over the ECDLP resource figures (`ResourceBounds.lean`,
`PointAddBenchmark.lean`, `SafegcdInversion.lean`, `KaratsubaMul.lean`). It re-derives no circuit.
Its single job is to make the **trust basis** of every quoted secp256k1 cost figure explicit, so that
no number is quotable without saying what stands behind it, and to present two figures side by side:

* a **verified floor** — the best end-to-end point-addition Toffoli figure composed ONLY of
  machine-verified and value-correct/anchored cost constants (no primitive accepted purely on the
  literature's authority);
* a **trusted estimate** — the best figure using the decades-audited textbook primitives (safegcd
  inversion, Karatsuba multiply, dedicated squaring), each cited to its source and NOT verified as a
  reversible circuit in this corpus.

The delta between the two is named the **verification frontier**: the primitives that are trusted but
not yet verified. The frontier is the roadmap, not a deficiency.

## The trust ladder (three tiers, precise)

* **verified** — machine-checked denote-level circuit correctness: a reversible circuit whose
  denotation is proved equal to the intended arithmetic value, with a derived gate cost. The
  carry-clean modular multiply `cleanModMulToffoli` (tied to `Reversible.cuccaroModMul` by
  `cleanModMulToffoli_eq_cuccaro`, value `Reversible.cuccaroModMul_correct : = X * Y mod N`) is the
  reference verified primitive; the carry-clean modular adder `Reversible.cuccaroModAdd_toffoli` is the
  reference verified adder.
* **anchored** — value-correct in `ZMod` plus a cost figure whose SUB-primitives are verified AND whose
  control-flow op-count is a PROVEN bound (a theorem), though no top-level circuit is exhibited. The
  Fermat inversion `fermatInvToffoli n = (2 * n) * cleanModMulToffoli n` is the reference: the value
  `a^(p-2) = a^(-1)` is a proved theorem (`ECDLP.fermatInv_eq_inv`, primality load-bearing), each field
  multiply is the verified `cleanModMulToffoli`, AND the `2 * n` square-and-multiply field-multiply count
  is a PROVEN bound (`ECDLP.fermatInvFieldMults_le : ≤ 2 * Nat.size e`, via `modExpFieldMults_le`), not
  merely documented. That proven op-count is exactly what earns `anchored` over `trusted`.
* **trusted** — a decades-audited construction accepted on the strength of the published literature,
  without a Lean circuit proof, cited to its source. In this corpus: the safegcd / Bernstein-Yang
  reversible GCD-inverse (`O(n^2)`); Gidney measurement-based uncomputation; the Karatsuba sub-quadratic
  multiply recurrence; windowed elliptic-curve scalar recoding. Each is a cost model whose leaf terms
  are anchored to verified gadgets, but whose ALGORITHM op-count is DOCUMENTED, NOT proven: safegcd's
  `2 * n` divstep count (`safegcdDivsteps`) has no termination/invariant proof (the divstep circuit is
  the named residue, 36c Case-C), and Karatsuba's recursion split is a `ring`-identity not a circuit
  fold. The proven-bound-vs-documented-count line is the distinction from `anchored`.

## The two headline figures (at `Secp256k1.bits = 256`, one affine point addition, classical offset)

* `secp256k1Toffoli_verifiedFloor    = 676880936`  (Fermat inversion, verified/anchored only)
* `secp256k1Toffoli_trustedEstimate  = 5831948`    (safegcd + Karatsuba + squaring, trusted primitives)

The verified floor is LARGER than the trusted estimate: the only inversion the corpus can machine-anchor
is Fermat, whose `O(n^3)` exponentiation dominates the point addition. The trusted estimate replaces it
with the `O(n^2)` safegcd inversion and the sub-quadratic Karatsuba multiply, dropping the figure by a
factor of about 116 (`two_track_gap_lower` / `two_track_gap_upper`). That factor of 116 IS the
verification frontier: it is exactly what verifying safegcd, Karatsuba, and measurement-based arithmetic
as reversible circuits would buy.

## Verifier versus estimator posture

The public ECDLP resource leaderboards are resource ESTIMATORS: they compose trusted textbook primitives
(Roetteler-Naehrig-Svore-Lauter 2017, eprint 2017/598; Haener-Jaques-Naehrig-Roetteler-Soeken 2020,
eprint 2020/077; Gidney 2023, arXiv 2306.08585), validated by small-instance simulation and peer review,
not by machine proof. This corpus VERIFIES the arithmetic at denote level, a different and harder
standard. The verified floor is the number this corpus can stand behind on that harder standard; the
trusted estimate is the number the estimator posture would report; the frontier is the named gap between
them. So the honest reading is not "N times off the leaderboard" (a verifier judged on the estimators'
axis) but "verified floor plus trusted reference estimate plus the named frontier between them".

The trusted-track figures below are literature-cited references, NOT corpus achievements: the corpus has
not verified the safegcd divstep circuit, the Karatsuba circuit, or measurement-based arithmetic.
-/

namespace ECDLP.ResourceBounds

open ECDLP

/-! ### The trust-basis ladder -/

/-- **The three-tier trust basis of a cost figure.**

* `verified` — machine-checked denote-level circuit correctness (a reversible circuit whose denotation
  is proved equal to the intended value, with a derived gate cost); the reference is the carry-clean
  modular multiply `cleanModMulToffoli` (`cleanModMulToffoli_eq_cuccaro`).
* `anchored` — value-correct in `ZMod` with verified sub-primitives AND a PROVEN control-flow op-count
  bound (no verified top-level circuit); the reference is the Fermat inversion `fermatInvToffoli` (proved
  value `ECDLP.fermatInv_eq_inv`, verified per-multiply, and the `2 * n` field-multiply count a PROVEN
  bound `ECDLP.fermatInvFieldMults_le`).
* `trusted` — a decades-audited construction accepted from the literature without a Lean circuit proof,
  cited to its source, whose ALGORITHM op-count is DOCUMENTED not proven: the safegcd / Bernstein-Yang
  GCD-inverse (`safegcdDivsteps = 2*n` with no termination proof), Gidney measurement uncomputation, the
  Karatsuba multiply recurrence, windowed elliptic-curve recoding. NOT verified in this corpus. The
  proven-op-count-bound (anchored) vs documented-op-count (trusted) line is what separates the two. -/
inductive TrustBasis
  | verified
  | anchored
  | trusted
  deriving DecidableEq, Repr

/-- **The named secp256k1 cost figures, as a finite tag domain.** Enumerates every figure this reporting
layer tags, so that `trustBasisOf` is total and no figure is quotable without its basis. -/
inductive EcdsaFigure
  /-- Carry-clean modular multiply Toffoli cost `cleanModMulToffoli n = 20*n^2 + 14*n` (verified). -/
  | cleanModMul
  /-- Carry-clean modular adder Toffoli cost `Reversible.cuccaroModAdd_toffoli = 12*n + 10` (verified). -/
  | cleanModAdd
  /-- Fermat modular inversion `fermatInvToffoli n = (2*n) * cleanModMulToffoli n` (anchored: verified
  per-multiply, and the `2*n` field-multiply count a PROVEN bound `ECDLP.fermatInvFieldMults_le`). -/
  | fermatInversion
  /-- Classical-offset coordinate term `classicalOffsetCoordToffoli` (anchored: verified adder, modelled count). -/
  | classicalOffset
  /-- The verified-floor point addition `onePointAddToffoli` (Fermat; verified + anchored only). -/
  | verifiedFloor
  /-- safegcd / Bernstein-Yang binary-GCD modular inversion `safegcdInvToffoli n = 60*n^2 + 28*n` (trusted). -/
  | safegcdInversion
  /-- Karatsuba sub-quadratic modular multiply recurrence `karatsubaToffoli` (trusted). -/
  | karatsubaMultiply
  /-- Dedicated Karatsuba-square modular squaring recurrence `squareToffoli` (trusted). -/
  | dedicatedSquaring
  /-- Gidney measurement-based adder re-cost `gidneyMeasAddToffoli = n` (trusted). -/
  | measurementAdder
  /-- The trusted-estimate point addition `onePointAddToffoli_squaring` (safegcd + Karatsuba + squaring). -/
  | trustedEstimate
  deriving DecidableEq, Repr

/-- **The trust basis of each named figure.** Total tagging: every `EcdsaFigure` carries its tier, so no
number is quotable without its basis. A composite figure (`verifiedFloor`, `trustedEstimate`) is tagged by
the JOIN of its components: `verifiedFloor` is `anchored` (its worst input is the anchored Fermat
inversion; it contains no `trusted` constant), and `trustedEstimate` is `trusted` (it contains safegcd and
Karatsuba inputs). -/
def trustBasisOf : EcdsaFigure → TrustBasis
  | .cleanModMul       => .verified
  | .cleanModAdd       => .verified
  | .fermatInversion   => .anchored
  | .classicalOffset   => .anchored
  | .verifiedFloor     => .anchored
  | .safegcdInversion  => .trusted
  | .karatsubaMultiply => .trusted
  | .dedicatedSquaring => .trusted
  | .measurementAdder  => .trusted
  | .trustedEstimate   => .trusted

/-! ### Track 1 — the verified floor (verified + anchored constants only) -/

/-- **The verified floor: one affine point addition, Fermat inversion.** The best end-to-end secp256k1
point-addition Toffoli figure the corpus can compose from `verified` and `anchored` constants ONLY, with
no primitive accepted purely on the literature's authority. It is the benchmark object `onePointAddToffoli`
(`PointAddBenchmark.lean`):

* three carry-clean field multiplies `3 * cleanModMulToffoli 256` — **verified**
  (`cleanModMulToffoli_eq_cuccaro`, value `Reversible.cuccaroModMul_correct`);
* one Fermat slope inversion `fermatInvToffoli 256` — **anchored** (value `ECDLP.fermatInv_eq_inv`
  proved, `2 * n` exponent schedule a documented op-count model);
* the classical-offset coordinate term `classicalOffsetCoordToffoli 256` — **anchored** (verified
  `cuccaroCModAdd` per-op cost, documented count of four `O(n)` subtractions).

It contains NO `trusted` (safegcd / Karatsuba / measurement) constant, so it is the honest conservative
machine-anchored number. It is conservative (large) precisely because the only inversion the corpus can
anchor is the `O(n^3)` Fermat exponentiation; that is what the frontier below would replace. -/
def secp256k1Toffoli_verifiedFloor : ℕ := onePointAddToffoli

/-- The verified floor evaluates to `676880936` Toffolis: the verified affine core
`affinePointOpToffoli 256 = 676866560` (one Fermat inversion `672923648` plus three carry-clean multiplies
`3 * 1314304 = 3942912`) plus the classical-offset coordinate term `14376`. -/
theorem secp256k1Toffoli_verifiedFloor_eq : secp256k1Toffoli_verifiedFloor = 676880936 := by
  rw [secp256k1Toffoli_verifiedFloor, onePointAddToffoli_eq]

/-- **The verified floor tags as `anchored`, never `trusted`.** Its worst-tier input is the anchored
Fermat inversion; it composes no `trusted` constant. -/
theorem verifiedFloor_trustBasis : trustBasisOf .verifiedFloor = .anchored := rfl

/-- **No trusted leak in the verified floor (the load-bearing honesty check).** Every component figure of
`secp256k1Toffoli_verifiedFloor` tags as `verified` or `anchored` — none is `trusted`. Decided over the
finite tag domain. -/
theorem verifiedFloor_no_trusted_leak :
    trustBasisOf .cleanModMul ≠ .trusted
    ∧ trustBasisOf .fermatInversion ≠ .trusted
    ∧ trustBasisOf .classicalOffset ≠ .trusted
    ∧ trustBasisOf .verifiedFloor ≠ .trusted := by decide

/-! ### Track 2 — the trusted estimate (best decades-audited primitives, literature-cited) -/

/-- **The trusted estimate: one affine point addition, safegcd inversion + Karatsuba multiply + dedicated
squaring.** The best-estimate secp256k1 point-addition Toffoli figure the corpus assembles, matching the
estimator posture by using the standard textbook primitives. It is `onePointAddToffoli_squaring`
(`KaratsubaMul.lean`):

* the modular inversion is the safegcd / Bernstein-Yang binary-GCD inverse `safegcdInvToffoli 256`
  (`O(n^2)`), replacing the anchored Fermat `O(n^3)`. **TRUSTED**: cited to Bernstein-Yang 2019 ("Fast
  constant-time gcd computation and modular inversion") and the reversible GCD-inverse of
  Roetteler-Naehrig-Svore-Lauter 2017 (eprint 2017/598). The corpus VALUE is a definitional unfolding of
  `ZMod.inv` (`binGcdInv_eq_inv`) and the `2 * n` divstep count is a documented model; the reversible
  divstep circuit is NOT verified in this corpus.
* the two general field multiplies are the Karatsuba sub-quadratic recurrence `karatsubaToffoli 256`
  (`Theta(n^1.585)`). **TRUSTED**: cited to Karatsuba-Ofman 1962. The recurrence SHAPE (3-way split) is
  documented; the divide-and-conquer reversible circuit is NOT verified in this corpus (its value rides on
  the verified schoolbook `Reversible.cuccaroModMul_correct`).
* the one squaring `lambda^2` is the dedicated Karatsuba-square recurrence `squareToffoli 256`. **TRUSTED**:
  the diagonal-symmetry halving is documented; no verified squaring circuit.

**This is a REFERENCE estimate, not a corpus achievement.** The corpus has NOT verified the safegcd
divstep circuit, the Karatsuba circuit, or the dedicated squaring circuit as reversible circuits. It is
presented to match the estimator posture, and every trusted input is cited above. It is NOT verified. -/
def secp256k1Toffoli_trustedEstimate : ℕ := onePointAddToffoli_squaring

/-- The trusted estimate evaluates to `5831948` Toffolis: the squaring-aware affine core
`affinePointOpToffoli_squaring 256 = 5817572` (two Karatsuba multiplies `2 * 653388 = 1306776`, one
dedicated squaring `571468`, one safegcd inversion `3939328`) plus the classical-offset coordinate term
`14376`. A literature-cited reference estimate, NOT a verified corpus figure. -/
theorem secp256k1Toffoli_trustedEstimate_eq : secp256k1Toffoli_trustedEstimate = 5831948 := by
  rw [secp256k1Toffoli_trustedEstimate, onePointAddToffoli_squaring_eq]

/-- **The trusted estimate tags as `trusted`, and its distinguishing inputs are trusted.** The safegcd
inversion, the Karatsuba multiply, and the dedicated squaring are each `trusted` (cited, not verified),
which is why the composite is `trusted` and not a corpus achievement. Decided over the finite tag
domain. -/
theorem trustedEstimate_uses_trusted :
    trustBasisOf .trustedEstimate = .trusted
    ∧ trustBasisOf .safegcdInversion = .trusted
    ∧ trustBasisOf .karatsubaMultiply = .trusted
    ∧ trustBasisOf .dedicatedSquaring = .trusted := by decide

/-! ### The verification frontier (the roadmap) -/

/-- **The verification frontier: the trusted primitives not yet verified as reversible circuits.** Each
entry is one future verification tranche — the delta between the verified floor and the trusted estimate,
made into a list of concrete targets. These are the constructions the trusted estimate uses and the
verified floor refuses. -/
def verificationFrontier : List String :=
  [ "safegcd divstep circuit: a reversible Bernstein-Yang (2019) / Roetteler-Naehrig-Svore-Lauter (2017, "
      ++ "eprint 2017/598) divstep recurrence whose denotation is the modular inverse, with a proved "
      ++ "GCD/Bezout invariant and termination. Currently the corpus value is a definitional unfolding of "
      ++ "ZMod.inv (binGcdInv_eq_inv) and the 2*n divstep count is a documented op-count model.",
    "measurement-based adder and multiply: Gidney (2018, Halving the cost of quantum addition) "
      ++ "measurement uncomputation at one Toffoli per bit. Not expressible in the measurement-free CCX "
      ++ "DSL; the corpus gidneyMeasAddToffoli handle costs only the measurement half (= n), the full "
      ++ "measurement-discipline circuit is not verified.",
    "sub-quadratic multiply circuit: a divide-and-conquer Karatsuba (Karatsuba-Ofman 1962) reversible "
      ++ "circuit whose denotation is X*Y mod N with the split and recombine proved. Currently the value "
      ++ "rides on the verified schoolbook cuccaroModMul_correct and the 3-way recurrence shape is "
      ++ "documented (karatsuba_identity is the algebra, not a circuit).",
    "windowed elliptic-curve scalar recoding: precomputed 2^i * P tables cutting additions "
      ++ "(Haener-Jaques-Naehrig-Roetteler-Soeken 2020, eprint 2020/077). Currently an op-count model, "
      ++ "not a verified windowed circuit." ]

/-- The verification frontier lists four named future tranches. -/
theorem verificationFrontier_length : verificationFrontier.length = 4 := rfl

/-! ### The gap (the frontier as a factor, not a deficiency) -/

/-- **The two-track gap, lower bracket.** The verified floor exceeds the trusted estimate by more than a
factor of 116: `secp256k1Toffoli_trustedEstimate * 116 < secp256k1Toffoli_verifiedFloor`
(`5831948 * 116 = 676505968 < 676880936`). The verified floor is the LARGER number because the only
inversion the corpus can machine-anchor is the `O(n^3)` Fermat exponentiation; the trusted estimate
replaces it with the `O(n^2)` safegcd inversion and the sub-quadratic Karatsuba multiply. -/
theorem two_track_gap_lower :
    secp256k1Toffoli_trustedEstimate * 116 < secp256k1Toffoli_verifiedFloor := by
  rw [secp256k1Toffoli_trustedEstimate_eq, secp256k1Toffoli_verifiedFloor_eq]; norm_num

/-- **The two-track gap, upper bracket.** The factor is below 117:
`secp256k1Toffoli_verifiedFloor < secp256k1Toffoli_trustedEstimate * 117`
(`676880936 < 5831948 * 117 = 682337916`). Together with `two_track_gap_lower` this pins the gap at about
116-fold. That factor of about 116 IS the verification frontier: it is exactly what verifying safegcd,
Karatsuba, and measurement-based arithmetic as reversible circuits would buy. The gap is the roadmap, not
a deficiency of the verified floor. -/
theorem two_track_gap_upper :
    secp256k1Toffoli_verifiedFloor < secp256k1Toffoli_trustedEstimate * 117 := by
  rw [secp256k1Toffoli_trustedEstimate_eq, secp256k1Toffoli_verifiedFloor_eq]; norm_num

/-- **The gap is strict.** The trusted estimate is strictly below the verified floor
(`5831948 < 676880936`) — the two tracks are genuinely different numbers, and the reporting layer keeps
them apart rather than quoting one as the other. -/
theorem trustedEstimate_lt_verifiedFloor :
    secp256k1Toffoli_trustedEstimate < secp256k1Toffoli_verifiedFloor := by
  rw [secp256k1Toffoli_trustedEstimate_eq, secp256k1Toffoli_verifiedFloor_eq]; norm_num

end ECDLP.ResourceBounds
