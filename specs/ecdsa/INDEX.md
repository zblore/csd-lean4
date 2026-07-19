# specs/ecdsa — the ecdsa.fail / ECDLP track index

The **ecdsa.fail quantum-cryptanalysis track** (elliptic-curve discrete-log cost
certification), separated from the CSD QM-reconstruction core. Code lives in
`CsdLean4/Ecdsafail/` (its own `Ecdsafail` lean_lib; not built by core QM). These are its
planning / status docs.

| Doc | What it is |
|---|---|
| [`ecdsafail-README.md`](ecdsafail-README.md) | **Entry point — read first.** The landing page for all ECDSA.fail work: the reversible EC point-addition subroutine the leaderboard scores, the verified-floor vs trusted-estimate two tracks, the improvement trajectory, and the file map. |
| [`ecdsafail-two-track.md`](ecdsafail-two-track.md) | The verified-floor / trusted-estimate two-track accounting: the trust ladder, the two headline figures, and the gap = the verification frontier. |
| [`ecdsafail-correlation.md`](ecdsafail-correlation.md) | Benchmark alignment: normalises the comparison to the ECDSA.fail scored object (one reversible point addition, `avg-Toffoli × peak-qubits`). |
| [`ecdsafail-optimization-plan.md`](ecdsafail-optimization-plan.md) | The tiered optimisation levers (verified-now / needs-DSL-extension / out-of-scope) toward the best verified result. |
| [`ecdlp-resource-plan.md`](ecdlp-resource-plan.md) | The ECDLP / reversible-arithmetic resource-accounting programme: the derived gate-list cost model toward verified Shor/ECDLP bounds on secp256k1. (Historical execution log — Tranches 1–7 + Phase 2 complete.) |

The true scored metric and leaderboard context are in `ecdsafail-README.md`. This track is
**not** part of the CSD reconstruction; the core `specs/BACKLOG.md` does not track it beyond
the optional final "separate repo" note.
