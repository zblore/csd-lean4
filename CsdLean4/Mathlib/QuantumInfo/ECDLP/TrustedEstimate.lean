import CsdLean4.Mathlib.QuantumInfo.ECDLP.TwoTrack

/-!
# Stage-1 trusted leaderboard estimate: measurement-uncompute + windowed EC, qubit model, score

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This is a **reporting layer** extension of `TwoTrack.lean`. It re-derives no circuit. Its job is to push the
trusted-track estimate down toward the public ecdsa.fail leaderboard band by **reproducing the leaders'
cited primitives** on top of the existing trusted estimate `secp256k1Toffoli_trustedEstimate = 5831948`
(safegcd inversion + Karatsuba multiply + dedicated squaring), and to compose a trusted SCORE (the
leaderboard metric, peak-qubits times Toffoli).

## CRITICAL HONESTY (read before quoting any number here)

Every figure in this file is `trusted`: a literature-cited reference, NOT a machine-verified corpus
figure and NOT a corpus achievement. The verified floor and the anchored figures of `TwoTrack.lean` /
`PointAddBenchmark.lean` are untouched.

The trusted route **REPRODUCES** the leaders' primitives as a cited reference; it does **NOT** beat them.
Beating the leaders needs a novel construction, which is research, not a reporting-layer re-cost. Reaching
the number-one entry exactly would mean reproducing the number-one construction. So the distinctive result
of this corpus is the VERIFIED entry (the verified floor, denote-level circuit correctness), not the
trusted rank computed here. A Lean cost figure is not a leaderboard submission: that needs the ecdsa.fail
harness run on the identical operation (the user's action, step 7 of the optimisation plan).

## The two cited reduction primitives (trusted, not verified in this corpus)

* **Gidney measurement-based uncomputation (factor 2).** Replacing each AND-uncomputation Toffoli by an
  X-basis measurement plus a CZ correction removes the reverse-pass Toffolis of the AND-heavy arithmetic,
  roughly halving the Toffoli cost of the multiply, squaring, and the safegcd divstep adders. The corpus
  handle `CSD.Empirical.QM.gidneyMeasAddToffoli = n` (exactly half the Cuccaro `2 * n`) is the adder-level
  witness of this factor. Cited to Gidney, "Halving the cost of quantum addition", Quantum 2 (2018) 74.
  The measurement-discipline circuit is NOT expressible in the corpus's measurement-free CCX DSL and is
  NOT verified here; the factor 2 is applied as a documented literature reduction.
* **Windowed elliptic-curve recoding (factor 2).** Windowed scalar recoding with precomputed multiples and
  a projective coordinate representation amortises the per-addition schedule, so the leaderboard's
  per-point-operation figure is a windowed-amortised number rather than a naive standalone affine addition.
  Applied here as a documented window factor 2 on the point-addition arithmetic. Cited to
  Roetteler-Naehrig-Svore-Lauter 2017 (eprint 2017/598) and Haener-Jaques-Naehrig-Roetteler-Soeken 2020
  (eprint 2020/077). The windowed circuit is NOT verified here.

## The trusted figures at `Secp256k1.bits = 256` (all trusted, all cited, none verified)

* `secp256k1Toffoli_measGidney         = 2915974`     (trusted estimate with Gidney factor 2)
* `secp256k1Toffoli_trustedEstimate_v2 = 1457987`     (Gidney factor 2 then windowing factor 2)
* `secp256k1Qubits_trustedEstimate     = 2304`        (= 9 * 256, documented layout, cited)
* `secp256k1Score_trustedEstimate      = 3359202048`  (= qubits * Toffoli, the ecdsa.fail metric)

## Where it lands vs the leaderboard (honest, from the arithmetic)

The public ecdsa.fail leaderboard best (late June 2026, corpus-recorded) is about `1152` peak qubits times
about `1360000` Toffoli, an exact product `leaderboardScoreExact = 1566720000` (the corpus's rounded handle
`ecdsaFailLeaderboardBest = 1570000000`).

* **Toffoli: essentially reproduced.** `secp256k1Toffoli_trustedEstimate_v2 = 1457987` is within about
  `1.08` times the leaders' `1360000` (slightly above). Same cited primitives, so this reproduces the
  leaders' Toffoli band, it does not beat it (`toffoli_v2_reproduces_leaderboard`).
* **Qubits: a factor of two above.** `secp256k1Qubits_trustedEstimate = 2304` is exactly `2 * 1152`
  (`qubits_trustedEstimate_two_leaderboard`). The modelled layout is the Roetteler-2017 / Haener-2020
  windowed-projective range (about `9n`), not the aggressive Litinski-2023 / Babbush measurement-based
  ancilla-recycling layout (about `4.5n`, about `1152`) that the number-one entry uses.
* **Score: about `2.14` times the number-one entry.** `secp256k1Score_trustedEstimate = 3359202048` sits
  between two and three times `leaderboardScoreExact` (`score_trustedEstimate_vs_leaderboard_lower` /
  `_upper`). The whole residual is the qubit factor of two; the Toffoli already reproduces the leaders.

**Honest rank.** The trusted score does NOT reach number one. It lands at about `2.14` times the number-one
score, with the Toffoli reproducing the leaders' band and the entire gap in the peak-qubit count. The
primitive that would close the residual is the aggressive measurement-based AND-ancilla-recycling qubit
layout of Litinski 2023 / Babbush et al. (about `4.5n` peak qubits); it is named and cited, not modelled
here, because modelling it would be reproducing the number-one construction, not a bounded re-cost. The
corpus records only the number-one leaderboard figure, so no specific top-N rank is claimed beyond the
number-one comparison the arithmetic supports.
-/

namespace ECDLP.ResourceBounds

open ECDLP

/-! ### Track 2b — the measurement-uncompute-adjusted Toffoli (trusted; Gidney 2018) -/

/-- **Trusted estimate with Gidney measurement-based uncomputation (factor 2): `2915974`.** The trusted
estimate `secp256k1Toffoli_trustedEstimate = 5831948` (safegcd + Karatsuba + squaring) with the Gidney
factor-2 halving of the AND-heavy uncompute passes applied. The corpus adder witness of the factor is
`CSD.Empirical.QM.gidneyMeasAddToffoli = n` (half of Cuccaro `2 * n`); cited to Gidney (2018). TRUSTED, a
cited literature reduction, NOT a verified circuit. -/
def secp256k1Toffoli_measGidney : ℕ := secp256k1Toffoli_trustedEstimate / 2

theorem secp256k1Toffoli_measGidney_eq : secp256k1Toffoli_measGidney = 2915974 := by
  rw [secp256k1Toffoli_measGidney, secp256k1Toffoli_trustedEstimate_eq]

/-! ### Track 2b — the windowed + measurement Toffoli (trusted; Haener 2020 / Roetteler 2017) -/

/-- **Trusted estimate, measurement-uncompute + windowed EC (factor 2 then factor 2): `1457987`.** The
Gidney-adjusted figure `secp256k1Toffoli_measGidney = 2915974` with the windowed-recoding factor-2
amortisation of the point-addition schedule applied. Equivalently `secp256k1Toffoli_trustedEstimate / 4`.
Cited to Roetteler-Naehrig-Svore-Lauter (2017, eprint 2017/598) and Haener-Jaques-Naehrig-Roetteler-Soeken
(2020, eprint 2020/077). TRUSTED, a cited literature reduction, NOT a verified circuit. This reproduces the
leaders' Toffoli band; it does not beat it. -/
def secp256k1Toffoli_trustedEstimate_v2 : ℕ := secp256k1Toffoli_measGidney / 2

theorem secp256k1Toffoli_trustedEstimate_v2_eq : secp256k1Toffoli_trustedEstimate_v2 = 1457987 := by
  rw [secp256k1Toffoli_trustedEstimate_v2, secp256k1Toffoli_measGidney_eq]

/-- **The v2 Toffoli is strictly below the existing trusted estimate.** `1457987 < 5831948`: the
measurement + windowing factors drop the figure by four. -/
theorem trustedEstimate_v2_lt_trustedEstimate :
    secp256k1Toffoli_trustedEstimate_v2 < secp256k1Toffoli_trustedEstimate := by
  rw [secp256k1Toffoli_trustedEstimate_v2_eq, secp256k1Toffoli_trustedEstimate_eq]; norm_num

/-! ### Track 2b — the trusted peak-qubit model (trusted; Roetteler 2017 / Haener 2020, Gidney 2018) -/

/-- **Trusted peak-qubit model: `9 * n = 2304` (documented layout, cited).** The score needs qubits, not
just Toffoli. Documented breakdown against the anchor `onePointAddPeakQubits = 11n + 6 = 2822`:

* `2n` — the quantum point coordinates `x, y`;
* `3n` — the field-arithmetic working registers (`Δx` inversion input, `Δy`, the accumulator);
* `3n` — the measurement-clean modular-multiply scratch bank, the anchor's `cleanModMulQubits = 6n + 6`
  bank roughly halved by Gidney (2018) measurement-based ancilla management;
* `n` — the windowed-recoding table register (Haener-Jaques-Naehrig-Roetteler-Soeken 2020).

Total `2n + 3n + 3n + n = 9n = 2304` at `n = 256`. This is the Roetteler-2017 / Haener-2020
windowed-projective range (about `9n`, cited counts about `2100` to `2330`), NOT the aggressive
Litinski-2023 / Babbush measurement-based ancilla-recycling layout (about `4.5n`, about `1152`) of the
number-one entry. TRUSTED, a documented layout model, NOT a verified layout. -/
def secp256k1Qubits_trustedEstimate : ℕ := 9 * Secp256k1.bits

theorem secp256k1Qubits_trustedEstimate_eq : secp256k1Qubits_trustedEstimate = 2304 := by
  norm_num [secp256k1Qubits_trustedEstimate, Secp256k1.bits]

/-- **The trusted qubit model is below the anchor `onePointAddPeakQubits = 2822`.** `2304 < 2822`: the
measurement-clean scratch halving nets a reduction even after the windowed-table register is added. -/
theorem qubits_trustedEstimate_lt_anchor :
    secp256k1Qubits_trustedEstimate < onePointAddPeakQubits := by
  rw [secp256k1Qubits_trustedEstimate_eq, onePointAddPeakQubits_eq]; norm_num

/-! ### Track 2b — the trusted score (trusted; the ecdsa.fail metric = peak-qubits times Toffoli) -/

/-- **The trusted score: `qubits * Toffoli = 3359202048`.** The ecdsa.fail leaderboard metric composed from
the two trusted factors, `secp256k1Qubits_trustedEstimate * secp256k1Toffoli_trustedEstimate_v2`. TRUSTED, a
cited reference, NOT a validated ecdsa.fail harness score (worst-case model versus their executed average;
harness run is the user's step 7). -/
def secp256k1Score_trustedEstimate : ℕ :=
  secp256k1Qubits_trustedEstimate * secp256k1Toffoli_trustedEstimate_v2

theorem secp256k1Score_trustedEstimate_eq : secp256k1Score_trustedEstimate = 3359202048 := by
  rw [secp256k1Score_trustedEstimate, secp256k1Qubits_trustedEstimate_eq,
    secp256k1Toffoli_trustedEstimate_v2_eq]

/-- **The trusted score is far below the existing trusted-estimate score.** `3359202048 < 16457757256`
(`onePointAddScore_squaring`): the measurement + windowing factors cut the score by about `4.9` times. -/
theorem score_trustedEstimate_lt_squaring_score :
    secp256k1Score_trustedEstimate < onePointAddScore_squaring := by
  rw [secp256k1Score_trustedEstimate_eq, onePointAddScore_squaring_eq]; norm_num

/-! ### The trust tags for the new figures (all trusted; nothing verified or anchored touched) -/

/-- **The Stage-1 trusted figures, as a finite tag domain.** Enumerates the new figures this extension tags,
so each is quotable only with its basis. Every one is `trusted` (cited, not verified). -/
inductive TrustedV2Figure
  /-- Gidney measurement-uncompute-adjusted Toffoli `secp256k1Toffoli_measGidney` (trusted; Gidney 2018). -/
  | measurementUncompute
  /-- Windowed EC recoding factor `secp256k1Toffoli_trustedEstimate_v2` (trusted; Haener 2020 / Roetteler 2017). -/
  | windowedEC
  /-- Trusted peak-qubit layout model `secp256k1Qubits_trustedEstimate` (trusted; documented layout). -/
  | trustedQubitModel
  /-- Composed trusted Toffoli v2 (trusted). -/
  | trustedEstimateV2
  /-- Composed trusted score (trusted; ecdsa.fail metric). -/
  | trustedScore
  deriving DecidableEq, Repr

/-- **The trust basis of each Stage-1 figure: all `trusted`.** Total tagging over the finite domain; no
figure is quotable without its basis, and every one is a cited literature reference, not a corpus
achievement. -/
def trustBasisV2 : TrustedV2Figure → TrustBasis
  | .measurementUncompute => .trusted
  | .windowedEC           => .trusted
  | .trustedQubitModel    => .trusted
  | .trustedEstimateV2    => .trusted
  | .trustedScore         => .trusted

/-- **The Stage-1 estimate uses only trusted inputs (the load-bearing honesty check).** Every new figure
tags as `trusted` (cited, not verified). Decided over the finite tag domain. No verified or anchored figure
is touched. -/
theorem trustedEstimate_v2_uses_trusted :
    trustBasisV2 .measurementUncompute = .trusted
    ∧ trustBasisV2 .windowedEC = .trusted
    ∧ trustBasisV2 .trustedQubitModel = .trusted
    ∧ trustBasisV2 .trustedEstimateV2 = .trusted
    ∧ trustBasisV2 .trustedScore = .trusted := by decide

/-! ### The leaderboard comparison (CONJECTURAL / EXTERNAL; honest rank from the arithmetic) -/

/-- **ecdsa.fail leaderboard best, Toffoli (EXTERNAL reference).** About `1360000` Toffoli per point
operation, the windowed-amortised figure of the leaderboard's best entry (late June 2026). CONJECTURAL /
EXTERNAL: not validated against the corpus circuit model. -/
def leaderboardToffoli : ℕ := 1360000

/-- **ecdsa.fail leaderboard best, peak qubits (EXTERNAL reference).** About `1152` peak qubits, the
aggressive measurement-based ancilla-recycling layout (about `4.5n`) of the leaderboard's best entry.
CONJECTURAL / EXTERNAL. -/
def leaderboardQubits : ℕ := 1152

/-- **ecdsa.fail leaderboard best, exact score = `1566720000`.** The metric `peak-qubits * Toffoli` of the
best entry, `leaderboardQubits * leaderboardToffoli` (the corpus's rounded handle is
`ecdsaFailLeaderboardBest = 1570000000`). CONJECTURAL / EXTERNAL. -/
def leaderboardScoreExact : ℕ := leaderboardQubits * leaderboardToffoli

theorem leaderboardScoreExact_eq : leaderboardScoreExact = 1566720000 := by
  norm_num [leaderboardScoreExact, leaderboardQubits, leaderboardToffoli]

/-- **Toffoli reproduces the leaderboard band (does not beat it).** The v2 Toffoli exceeds the leaders'
figure (`1360000 < 1457987`) and is within about `1.08` times it
(`secp256k1Toffoli_trustedEstimate_v2 * 100 < leaderboardToffoli * 108`, `145798700 < 146880000`). Same
cited primitives (safegcd + Karatsuba + Gidney measurement + windowing), so the v2 Toffoli REPRODUCES the
leaders' Toffoli band, slightly above; it does not beat it. -/
theorem toffoli_v2_reproduces_leaderboard :
    leaderboardToffoli < secp256k1Toffoli_trustedEstimate_v2
    ∧ secp256k1Toffoli_trustedEstimate_v2 * 100 < leaderboardToffoli * 108 := by
  rw [secp256k1Toffoli_trustedEstimate_v2_eq, leaderboardToffoli]
  refine ⟨by norm_num, by norm_num⟩

/-- **The trusted qubit model is exactly twice the leaderboard peak-qubit count.**
`secp256k1Qubits_trustedEstimate = 2 * leaderboardQubits` (`2304 = 2 * 1152`). The entire score residual to
the number-one entry is this factor of two: the modelled Roetteler-2017 / Haener-2020 windowed-projective
layout (about `9n`) versus the aggressive Litinski-2023 / Babbush layout (about `4.5n`). -/
theorem qubits_trustedEstimate_two_leaderboard :
    secp256k1Qubits_trustedEstimate = 2 * leaderboardQubits := by
  rw [secp256k1Qubits_trustedEstimate_eq, leaderboardQubits]

/-- **The trusted score lands above two times the number-one score (lower bracket).**
`leaderboardScoreExact * 2 < secp256k1Score_trustedEstimate` (`3133440000 < 3359202048`). The trusted score
does NOT reach the number-one entry. -/
theorem score_trustedEstimate_vs_leaderboard_lower :
    leaderboardScoreExact * 2 < secp256k1Score_trustedEstimate := by
  rw [leaderboardScoreExact_eq, secp256k1Score_trustedEstimate_eq]; norm_num

/-- **The trusted score lands below three times the number-one score (upper bracket).**
`secp256k1Score_trustedEstimate < leaderboardScoreExact * 3` (`3359202048 < 4700160000`). Together with the
lower bracket this pins the trusted score at about `2.14` times the number-one entry. The whole residual is
the qubit factor of two (the Toffoli already reproduces the leaders); closing it needs the aggressive
measurement-based ancilla-recycling qubit layout of Litinski 2023 / Babbush et al. (about `4.5n` peak
qubits), which is reproducing the number-one construction, not a bounded re-cost. -/
theorem score_trustedEstimate_vs_leaderboard_upper :
    secp256k1Score_trustedEstimate < leaderboardScoreExact * 3 := by
  rw [leaderboardScoreExact_eq, secp256k1Score_trustedEstimate_eq]; norm_num

/-- **The trusted score also sits between two and three times the corpus rounded leaderboard handle.**
`ecdsaFailLeaderboardBest * 2 < secp256k1Score_trustedEstimate < ecdsaFailLeaderboardBest * 3`
(`3140000000 < 3359202048 < 4710000000`). Consistent with the exact-factor brackets above. -/
theorem score_trustedEstimate_vs_rounded_leaderboard :
    ecdsaFailLeaderboardBest * 2 < secp256k1Score_trustedEstimate
    ∧ secp256k1Score_trustedEstimate < ecdsaFailLeaderboardBest * 3 := by
  rw [secp256k1Score_trustedEstimate_eq]
  refine ⟨by norm_num [ecdsaFailLeaderboardBest], by norm_num [ecdsaFailLeaderboardBest]⟩

end ECDLP.ResourceBounds
