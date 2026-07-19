# CsdLean4/Ecdsafail — the ecdsa.fail quantum-cryptanalysis track

**This folder is NOT part of the CSD QM-reconstruction core.** It is the separate
ecdsa.fail / ECDLP quantum-cryptanalysis project (elliptic-curve discrete-log cost
certification: point add/double, scalar multiplication, safegcd modular inversion,
secp256k1, Toffoli/qubit resource bounds).

## Contents (21 modules)

- **ECDLP** (17): `EllipticCurve`, `Secp256k1`, `PointAdd`, `PointDouble`, `ScalarMul`,
  `Inversion`, `SafegcdInversion`, `SafegcdDivstep{,Circuit}`, `SafegcdExecCost`,
  `HalfGcdInversion`, `KaratsubaMul`, `ResourceBounds`, `TwoTrack`, `ThreeTrackScore`,
  `TrustedEstimate`, `PointAddBenchmark`.
- **ecdsa-specific circuit assembly** (4, moved out of `Reversible/`): `ProgramRouter`,
  `ProgramRouterDoubling`, `DoublingAssembly`, `DoublingAssemblyOps`.

## Boundary

- **Depends on** the shared reversible-arithmetic DSL in
  `CsdLean4/Mathlib/QuantumInfo/Reversible/` (`CuccaroAdd`, `ModMul`, `ModInv`, …), which
  stays in core because core-QM (Shor + the measurement-adder empirical modules) also use it.
- The **core aggregator `CsdLean4.lean` does not import this folder** — `lake build CsdLean4`
  builds only core QM. These modules are built via `Tests/AxiomAudit.lean` (the only
  remaining inbound edge) and direct `CsdLean4.Ecdsafail.*` targets.
- The core honesty guard (`scripts/check-claims.sh`) **excludes** this folder.

## Remaining for a full project split

Own `lean_lib` target (or separate repo), and move the ecdsa `#print axioms` pins out of the
core `Tests/AxiomAudit.lean`. See `specs/BACKLOG.md` → "ecdsa.fail separation".
