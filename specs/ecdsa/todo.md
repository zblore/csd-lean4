# ECDSA.fail track — task ledger (historical)

> Moved from specs/active-todo.md 2026-07-19. The ecdsa.fail / ECDLP task rows (mostly DONE execution record). Code in `CsdLean4/Ecdsafail/`; see also [`score-ledger.md`](score-ledger.md), [`ecdsafail-README.md`](ecdsafail-README.md).

| # | Task | Cat | Cx | Status | Blocked |
|---|---|---|---|---|---|
| 11 | ECDSA L6 safegcd inversion (dominant) | ECDSA | L | DONE | |
| 12 | ECDSA L1 Karatsuba multiply | ECDSA | M | DONE | |
| 13 | ECDSA L2 windowed Fermat (comparison) | ECDSA | S | DONE | |
| 10 | ECDSA L3 shared-partial-product squaring | ECDSA | M | DONE | |
| 2 | ECDSA L1–L6 (umbrella) | ECDSA | — | open | #14 |
| 18 | L5-a measure-and-correct primitive (amplitude model) — GREEN LIGHT: measurement-based uncompute IS verifiable in Lean | ECDSA | M | DONE | |
| 19 | L5-b ~2× cost accounting + operator↔list link | ECDSA | S–M | DONE | |
| 20 | L5-c Boolean↔amplitude bridge — SCOPING DONE, verdict WALL (see below) | ECDSA | L–XL | scoped (wall) | |
| 30 | AND-based adder primitive (Boolean DSL; fresh per-carry AND temporary) — DONE (the L5-d attachment point) | ECDSA | L | DONE | |
| 31 | Localized amplitude lift of the AND-uncompute block (denote↔toEuclideanLin, restricted) — DONE: L5-c wall closed at CELL granularity (MeasurementUncomputeLift.lean) | ECDSA | L–XL | DONE | #30 |
| 21 | L5-d measurement-based adder re-cost — DONE: adder Toffolis 6n→3n (n=256: 1536→768), aggregated from 3n #31-proven-equivalent blocks (MeasurementAdder.lean); n-fold amplitude correctness WALLED (gadget non-permutation; QReg 3⊗QReg(m−3) tensor factor); SCORE still gated on adder-swap-through-point-addition + #7 | ECDSA | M | DONE | #7 |
| 22 | L5-e DSL-extension posture decision | ECDSA | M | open | #18 |
| 35 | Minimal 1-Toffoli-per-carry Gidney adder — DONE: `gidneyAdd_correct = (a+b) mod 2ⁿ` (FULL general-n Boolean correctness, anti-hollow), 1-Toffoli `majCell`, unitary `2n` (ties Cuccaro), measurement re-cost `n` (`gidney_beats_cuccaro` vs proven corpus Cuccaro `2n` + #30 `6n`; n=256: 256/512/1536); space tradeoff O(n) disclosed; GidneyAdder.lean + MeasurementGidneyAdder.lean | ECDSA | L | DONE | |
| 36a | VerifiedAdder interface + adder-parametric generic multiplier — DONE: `genMul_correct` (parametric fold induction), `genMul_toffoli = n·A.toffoli`; faithfulness `genMul corpusAdder = mulLoop` (rfl) recovering `30n²` exactly (non-lossy). Interface at the Horner-STEP level (VerifiedAdder.lean). HONEST LIMIT (scout): abstracts the FOLD only — a cheaper BASE adder does NOT propagate by instantiation (modAdd/cModAdd/modDouble sit between; 36b must re-derive the step), and the carry-clean memory model needs a VARIANT interface | ECDSA | M | DONE | #35 |
| 36b | Carry-clean VerifiedAdder variant — DONE: `VerifiedAdderCarryClean` (global restored-clean invariant: clean precondition + `cleanRestored` postcondition threaded; NOT 36a's fresh-ancilla `cleanStable`), `genMulCC_correct` parametric, faithfulness `genMulCC cuccaroAdder = cuccaroModMul` (rfl) recovering `20n²+14n` exactly. Fully Boolean-verified, no amplitude wall. Θ(n)-qubit win genuine (VerifiedAdderCarryClean.lean). Keystone proven to generalise across memory models | ECDSA | M | DONE | #36a |
| 36c | Generic inverter — SCOUTED (Case C): NEITHER inverter is a verified gate-level CIRCUIT. Fermat (`Inversion.lean`) = ZMod value-correct (`fermatInv_eq_inv`) + op-count cost-figure (`2n·perMultiply`), NO square-and-multiply circuit. Safegcd (`SafegcdInversion.lean`) = value-correct-by-unfolding + verified-gadget-anchored per-divstep × DOCUMENTED count, NO divstep circuit folded (module defers it). So 36c cannot be a 36a-style abstraction (no concrete inverter-circuit to recover); a cost-only parametric inverter fails ⟦c⟧=op (NOT built). OPTIONS: (1) build the Fermat square-and-multiply CIRCUIT over genMul/genMulCC — anti-hollow, FIRST verified inverter circuit, but O(n³) and NOT the score's term (staged 36c-1 squaring / 36c-2 exponent fold / 36c-3 faithfulness; the in-place B←B² clean-uncompute is the genuine new hard part); (2) build the safegcd divstep CIRCUIT — the score's actual O(n²) term, gold-standard but heaviest (Bernstein-Yang divstep invariant + termination); (3) cost-recurrence-only — REJECTED (hollow). HONEST TENSION: the cheap inverter the score uses (safegcd) has no circuit; the one buildable from the parametric multiply (Fermat) is O(n³) and not the score's term. None moves the benchmark NUMBER without harness #7. **DECISION 2026-07-16: option (2) chosen — build the safegcd divstep CIRCUIT (`denote = divstep`). TRANCHES 1–3 DONE** (`SafegcdDivstepCircuit.lean`): (1) exact-halving primitive as a concrete `n`-swap `Circuit`, `denote`-correct (`halve_correct`: even register → `regValRange/2`, general n) and Toffoli-FREE (`shiftDown_toffoli`, refines the `cuccaroModDouble` 6n+4 halving overcount to 0); (2) signed integer arithmetic — `signedRep`/`regValZ` two's-complement decoder + `signedAdd_correct`/`signedSub_correct` (under no-overflow, verified mod-2^n `cuccaroAdd`/`rippleSub` realise the `g+f`/`g-f` numerators at the signed-ℤ level); (3) branch control — `cswap`(Fredkin)/`condSwapReg` controlled register swap (`condSwapReg_swaps`: `f↔g` iff control set, 1 Toffoli/bit) + `Odd g` test as a wire-0 read (`regValRange_odd_iff`/`regValZ_odd_iff`); (4a) SIGNED halving — building the assembly exposed that T1's `shiftDown` is UNSIGNED (fills top with 0) but the divstep halves SIGNED `(g±f)/2` (g,f negative), so `signedHalve` (sign-extending shift) + `signedHalve_correct` (`regValZ ÷2`, even reg), with `signedRep_high`/`regValZ_signBit` two's-complement support; (4b) g-update composition — `gUpdateSub_correct`/`gUpdateAdd_correct` compose T2+T4a into ONE circuit computing `g ↦ (g∓f)/2` at the signed `regValZ` level (f,g odd ⇒ even numerator discharges the halve's bottom-bit hyp); (4c) the `0<δ` control read — `regValZ_pos_iff`/`regValZ_nonneg_iff` characterise the branch discriminant `0<δ` as a bit read (sign clear + low bits nonzero), via `regValZ_signBit`; (4d) δ-counter update `δ↦1±δ` — `deltaInc_correct`/`deltaDec_correct`, a T2 corollary (signed ± vs constant 1). So EVERY divstep sub-operation is circuit-backed (swap, signed ±, signed halve, g-update, δ-update, 0<δ / Odd g reads); (4e) reversible nonzero/OR gadget `orAccum_correct` (the "low bits≠0" half of 0<δ); (4f) branch-A f-recovery `addTwice_correct` (f←f+2g) + `branchA_recovers` (f+2·((g-f)/2)=g) — resolves the in-place f'=g (g-update first, then recover, no swap), so gUpdateSub+addTwice compose to branch A. Branch A's in-place (f,g) transform is now circuit-backed. (4g) lane-0 cswap elision `cswap_lane0_noop` (frontier's `divstep 0..n→1..n` Toffoli lever, proved value-exact); (4h) branch-control-bit synthesis `and3_correct` (bA = sign_clear ∧ nonzero_δ ∧ odd_g into a clean ancilla). Remaining T4 residual: controlled (branch-gated) gadget variants + wiring, then end-to-end denote = `divstepRev`. Three-track SCORE ledger added (ThreeTrackScore.lean): Leaderboard-convention = 1.58e9 PARITY (competition metric; TRUSTED PROJECTION — avg-executed ADOPTED from the frontier's own measured value, NOT computed here; a real figure needs #7). | ECDSA | XL | in progress (T1–T4h done; full assembly remains) | #36a,#36b |
| 36d | Instantiate the Gidney measurement adder (amplitude-gated per #21/#31) for the further drop; re-cost vs ResourceBounds | ECDSA | M | open | #36b |
| 14 | ECDSA L5 Gidney measurement adders (Tier-X umbrella) — score lever ONLY after #35 + pervasive O(n²) mult/inverter application | ECDSA | XL | open | #35,#7,#22 |

| 7 | ECDSA step 2: run their Rust harness (USER action) | ECDSA (user) | S | open | |

---

## L5-c wall CLOSED at cell granularity (2026-06-30, #31)

`CsdLean4/Empirical/QM/MeasurementUncomputeLift.lean` (auditor-SOUND, foundational-triple, no busch).
The L5-c "no gate-lift" obstruction (1, below) is closed FOR THE SINGLE AND-uncompute block by staying
in L5-a's `B3 = Fin 3 → Fin 2` permutation-matrix representation — NO `Fin 8`/`qmToffoli` reindex (that
ill-typing was exactly the wall). Headlines, all computed not asserted:
- `andUncompMat_lifts_denote` — the `B3` unitary acts on basis states exactly as the Boolean Toffoli
  `denote (andUncompute 0 1 2)` (modulo an explicit, round-tripping `Bool↔Fin 2` recast). The localized
  gate-lift.
- `andUncompMat_uncomputes` — the unitary deterministically uncomputes the AND on the `andInput` subspace
  (`toEuclideanLin andUncompMat (andInput c) = uncomputedData c 0`).
- `andUncompute_measureUncompute_agree_on_block` / `..._same_data` — the unitary block and the L5-a
  measurement gadget land in the SAME `uncomputedData c ·` family (same data amplitudes `c`; ancilla `0`
  deterministic vs `m` measured; the `_same_data` form clears the `(√2)⁻¹` so `c` is literal in both).
  So `measureUncompute` is a PROVEN-equivalent replacement on this block.
- `andUncompute_measurement_saving` — 1 vs 0 Toffoli, on the proven-equivalent block (not a count over an
  unverified swap; the auditor confirmed this is the real saving, not 0-vs-0/miscount).

Honest scope: CELL granularity. Trusted base grows by this localized lift. NO circuit-level re-cost and
NO ECDSA score change here. DEFERRED: #21 (L5-d) threads the block-replacement through the AND-based
adder's `n` AND-uncomputes for the circuit re-cost (gap ~10.5×→~5×); the watch-point (auditor) is whether
the per-block "same data modulo ancilla/scalar" composes coherently across the `n`-fold tensor embedding
(stay in the per-block `B3` factor, identity elsewhere — the analogous sidestep). Also gated on #7 (harness).

## L5-c scoping probe verdict (2026-06-29) — WALL [superseded at cell granularity by #31 above]

The measurement-based AND-uncompute (L5-a/b, verified as an amplitude gadget, `measureUncompute_cost`:
0 vs 1 Toffoli per AND) is currently STRANDED in the amplitude model with no attachment point to corpus
arithmetic. Two obstructions:
1. **No gate-lift.** `denote : (Fin n → Bool) → (Fin n → Bool)` (Boolean permutation) and the amplitude
   unitaries (`qmToffoli : Matrix (Fin 8)`) are ill-typed against each other: bridging needs a `Bool≃Fin 2`
   recast, per-gate `Equiv.Perm (Fin n → Fin 2)` packaging, and a general amplitude-lift `denote c ↔
   toEuclideanLin (∏ permMatrix)` (a real 2ⁿ-dim isometry, foundational but a nontrivial induction over
   the gate list). The clean `Equiv.Perm.permMatrix` pattern exists (LF5 `vnUnitary_mulVec_single`) but is
   generic — it touches neither `qmToffoli` nor `denoteGate`.
2. **Decisive: no AND-ancilla to discharge.** The corpus Cuccaro adder is IN-PLACE carry-restoring (`uma`
   uncomputes the carry UNITARILY); there is no fresh `|0⟩`-initialised AND temporary. Gidney's gadget
   needs an AND-based adder (one fresh AND ancilla per carry, later measured away). So even with a perfect
   gate-lift, `measureUncompute` has nothing to attach to.

**Consequence: L5-d is NOT a re-cost.** The Tier-X parity path requires NEW INFRASTRUCTURE:
- **#30** an AND-based adder primitive in the reversible DSL (a Boolean task, no amplitude bridge: allocate
  + compute + later uncompute a per-carry AND temporary, so an `andInput`-shaped state appears at an
  uncompute point);
- **#31** a LOCALIZED amplitude lift of just that AND-uncompute block (not a full general-circuit `denote`
  lift), bridging the single block via the `permMatrix` pattern;
- then **#21 (L5-d)** re-costs the AND-based adder with `measureUncompute` replacing the AND-uncompute Toffoli.

Honest L5 status: measurement-based uncompute is VERIFIED as an amplitude gadget (L5-a/b done) with a real
per-gadget Toffoli saving; APPLYING it to corpus arithmetic for a score is gated on #30 + #31 — genuine new
construction (the trusted base grows), NOT a wrapper. This is the user-gated fork's true cost, now known.
