# ECDLP / reversible-arithmetic resource-accounting programme — plan + live status

**STATUS: Tranche 1a DONE 2026-06-19 (`Circuit.lean` GREEN + committed); Tranche 1b (`Cost.lean`)
NEXT.** The build blocker is resolved (see below).

---

## ✅ RESUME STEP 0 — the build blocker (RESOLVED 2026-06-19)

The blocker was **Smart App Control** (Windows 11 Home), not AppLocker/WDAC: a pending SAC enforce
policy activated 3 seconds after a reboot (CodeIntegrity event 3099), so the unsigned Lean
toolchain (`~/.elan/.../lake.exe`) was rejected (events 3077/3033, "did not meet the Enterprise
signing level requirements", Policy ID `{0283ac0f-...}`). SAC has no per-app allowlist and is a
one-way toggle. **Fixed by turning Smart App Control Off** (Windows Security → App & browser
control → Smart App Control settings → Off); `lake` ran immediately, no reboot needed. Diagnosis
key for the future: `VerifiedAndReputablePolicyState` under `HKLM:\SYSTEM\CurrentControlSet\Control\CI\Policy`
(1 = SAC enforcing, 0 = off).

The historical error was:
```
error: command failed: 'lake.exe'
info: caused by: An Application Control policy has blocked this file. (os error 4551)
```

---

## Goal

Extend the existing quantum-algorithm tier toward verified **ECDLP / Shor resource accounting**
on secp256k1. NOT re-proving Shor; building the missing reversible-arithmetic + elliptic-curve +
cost-accounting bridge. Cat-1/Cat-2 infrastructure, **CSD interpretation kept out** of this layer.
Two passes: **Pass 1** = sorry-free semantic scaffold + *abstract* cost bounds; **Pass 2** =
concrete reversible circuits with *exact* Toffoli/qubit/depth counts. Honest claim after Pass 1:
"a sorry-free semantic + abstract resource scaffold for ECDLP over secp256k1." NOT "a verified
fault-tolerant attack" — that needs Pass 2's real circuits.

## Investigation map (done 2026-06-18) — reuse wins

- **EC group law is FULLY in Mathlib.** `WeierstrassCurve.Affine.Point` has `add`, `neg`, the
  `nonsingular`/membership predicate, and **`instance : AddCommGroup W.Point`**
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:777`), plus Projective/Jacobian
  models + division polynomials. **Tranche 5 must NOT reprove the group law** — wrap Mathlib's.
- **Modular inverse is in Mathlib.** `ZMod.inv`, `mul_inv_eq_gcd`, `unitOfCoprime`,
  `coe_unitOfCoprime`, `mul_inv_of_unit` (`Mathlib/Data/ZMod/Basic.lean`). **Tranche 4 semantic
  layer is reuse.**
- **Shor already has the modular-mult permutation oracle:** `mulOracle : |y⟩ ↦ |a·y⟩` on
  `EuclideanSpace ℂ (ZMod N)` for `a : (ZMod N)ˣ` (`Empirical/QM/Algorithms/ShorCore.lean`), with
  NO gate-level decomposition or cost. That is exactly the gap this programme fills; `mulOracle`
  is the semantic target for Tranche 3.
- No existing circuit-cost/Toffoli layer (the corpus `resource`/`cost` files are LOCC/entanglement
  resources, not gate counts). Tranche 1 is greenfield.
- Algorithm tier (reuse): `Mathlib/QuantumInfo/{Register,Hadamard,Fourier}.lean`,
  `Empirical/QM/Algorithms/{DeutschJozsa,Grover,ShorCore,ShorRecovery,ShorRandomA,ShorCapstone}.lean`.

## DESIGN DECISION (locked): derived gate-list cost model

Costs are **derived from the gate list**, not annotated onto opaque `Equiv`s. A circuit is a
`List Gate`; its action is the fold of per-gate semantics; its cost is a *function* of the gate
list. So "op costs ≤ B Toffolis" is a theorem (exhibit `c`, prove `⟦c⟧ = op` ∧ `cost c ≤ B`),
not a trusted number. This is what makes the two-pass plan real: Pass 1 states bounds abstractly
(circuit not yet exhibited); Pass 2 exhibits the circuit and discharges them. (Annotated costs
were rejected — they make "verified resource accounting" hollow.)

## File paths

```
CsdLean4/Mathlib/QuantumInfo/Reversible/Circuit.lean   -- Tranche 1a: gate DSL + denote + inverse  [DONE 2026-06-19, GREEN]
CsdLean4/Mathlib/QuantumInfo/Reversible/Cost.lean      -- Tranche 1b: Cost record + circuitCost + comp lemmas  [TODO]
CsdLean4/Mathlib/QuantumInfo/Reversible/ModAdd.lean    -- Tranche 2
CsdLean4/Mathlib/QuantumInfo/Reversible/ModMul.lean    -- Tranche 3 (target: Shor mulOracle)
CsdLean4/Mathlib/QuantumInfo/Reversible/ModInv.lean    -- Tranche 4 (reuse ZMod.inv)
CsdLean4/Mathlib/QuantumInfo/ECDLP/EllipticCurve.lean  -- Tranche 5 (wrap Mathlib WeierstrassCurve)
CsdLean4/Mathlib/QuantumInfo/ECDLP/ScalarMul.lean      -- Tranche 6 (double-and-add over Mathlib group)
CsdLean4/Mathlib/QuantumInfo/ECDLP/Secp256k1.lean      -- Tranche 7
CsdLean4/Mathlib/QuantumInfo/ECDLP/ResourceBounds.lean -- abstract (Pass 1) -> exact (Pass 2)
CsdLean4/Tests/ECDLPAudit.lean                         -- pins; ADD root to lakefile.toml CsdLeanTests
specs/ecdlp-resource-plan.md                           -- this file
```
Namespace inside: natural (`Reversible`, `ECDLP`, reuse `WeierstrassCurve`), NOT `QuantumInfo.*`
or CSD. Note: EC arithmetic isn't "quantum"; `ECDLP/` under `QuantumInfo/` is a staging-cohesion
choice only. New `Tests/ECDLPAudit.lean` must be added to `lakefile.toml`'s `CsdLeanTests` roots.

## Tranche 1 status

**1a — `Circuit.lean` (DONE 2026-06-19, GREEN, 0 sorry, 0 warnings):**
- `Gate n` = `X i | CX c t | CCX c₁ c₂ t | swap i j` (deriving DecidableEq); `State n = Fin n → Bool`.
- `denoteGate` (degenerate control=target ⇒ identity, so every gate is an involution);
  `denoteGate_involutive`.
- `Circuit n = List (Gate n)`; `denote` (foldl); `denote_append` / `reversible_comp_correct`;
  `inverse = List.reverse`; `reversible_inverse_correct` (+ `'` right form); `denote_bijective`.
- **Four proof bugs from the unverified draft, all fixed on first build:** (1) `reversible_inverse_correct'`
  used a `List.reverse_reverse` rewrite that didn't fire — replaced with `inverse (inverse c) = c`;
  (2) `denote_bijective` injective half needs the *unprimed* `reversible_inverse_correct` (the
  `LeftInverse`), only surjective uses the primed one; (3) the cons case of `reversible_inverse_correct`
  had `simp` unfold `inverse`, breaking the `ih` match — restructured through
  `inverse (g :: c) = inverse c ++ [g]`; (4) CCX involution used `cases s t` after `subst hk` had
  eliminated `t` in favour of `k` — `cases s k`. Two redundant `if_pos`/`if_neg` simp args trimmed.

**1b — `Cost.lean` (TODO):** `structure Cost` (qubits, ancilla, toffoli, toffoliDepth, cnot,
tCount, meas, all ℕ); `gateCost : Gate n → Cost` (X→0; CX→cnot 1; CCX→toffoli 1, toffoliDepth 1;
swap→cnot 3); `circuitCost c` field-wise via `(c.map (fun g => (gateCost g).field)).sum` (avoids
needing an `AddMonoid Cost` instance), with `qubits := n`, `ancilla := 0`. Comp lemmas:
`cost_comp_toffoli_count` (`= +`, via `List.map_append`+`List.sum_append`),
`cost_comp_toffoli_depth_le` (`≤ +`, holds with equality), `cost_comp_qubits_le`
(`≤ max`, = `n ≤ max n n`, trivial — width/ancilla accounting is a later refinement, documented).

## Resume checklist
0. ~~Clear the `lake.exe` Application Control block~~ **DONE (SAC off).**
1. ~~Build `Circuit.lean`; fix the involution proofs~~ **DONE 2026-06-19 (4 fixes, green, committed).**
2. Write + build `Cost.lean`. **← NEXT**
3. Add both modules to `CsdLean4.lean`; add AxiomAudit pins (or `Tests/ECDLPAudit.lean` + lakefile root).
   (Note: `Circuit.lean` is NOT yet in the import graph — it builds standalone but is not reached by
   `lake build`; wire it in with `Cost.lean` in step 3 so CI covers it.)
4. Audit (csd-lean-auditor): involutions genuine, `reversible_inverse_correct` real, costs derived
   not annotated, no sorry/axiom.
5. Commit Tranche 1; update this file + `specs/INDEX.md`. Then Tranche 2 (ModAdd).
