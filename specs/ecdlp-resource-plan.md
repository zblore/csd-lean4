# ECDLP / reversible-arithmetic resource-accounting programme — plan + live status

**STATUS: PROGRAMME COMPLETE 2026-06-21 — ALL 7 TRANCHES DONE, GREEN, wired + AxiomAudit-pinned, each
auditor-reviewed SOUND.** T1 Circuit/Cost (reversible-gate DSL + derived cost model). T2 ModAdd (cost +
full `(A+B) mod 2^n` correctness). T3 ModMul (mulConst + multiplier cost + `mulCircuit_correct` `Acc=a·Y`
+ modular oracle `mulCircuit_correct_zmod`). T4 ModInv (inverse oracle + algebra + reversibility link;
no inversion circuit). T5 EllipticCurve (`scalarMul [k]P` + ECDLP statement, wraps WeierstrassCurve). T6
ScalarMul (`doubleAndAdd` + correctness + O(log k) cost). **T7 CAPSTONE** (`Secp256k1.lean` +
`ResourceBounds.lean`): the secp256k1 curve `y²=x³+7` over `𝔽_p` (`p=2^256−2^32−977`) + the end-to-end
estimate `secp256k1_scalarMul_toffoli_bound` (`[k]P ≤ 2·256·(M·(2·256·256)) = O(256³)·M` Toffolis),
composing T6's O(log k) op count and T3's `2n²` multiplier — auditor SOUND, non-vacuous (numeric bound
`≤ 2^26` at M=1). **`M` fixed (Pass-1, 2026-06-22):** `pointOpMults = 16` (documented EFD field-mult count
per projective `a=0` point op) collapses the estimate to the concrete figure `secp256k1ToffoliBound =
2^30 = 1 073 741 824` Toffolis (`secp256k1_scalarMul_toffoli_concrete`) — an UPPER-BOUND figure (omits
mod-`N` reduction; assumes the standard formulae whose circuit correctness is Pass-2 residue), NOT an
attack cost. **Refined 2026-06-22:** per-op-type weighting (`doubleAndAddWeightedCost`; doubling 7 field
mults / mixed addition 11, EFD `a=0`) tightens this to `secp256k1ToffoliRefined = 603 979 776 ≈ 6.0×10^8`
(`secp256k1_scalarMul_toffoli_refined`), ~1.8× below uniform-`M`. The ripple adder is already
Cuccaro/Takahashi-class (2 Toffoli/bit; not halvable without measurement-based uncomputation, absent from
the DSL); the residual gap to the most-optimised literature is the DOCUMENTED un-formalised optimisations
(windowing, Montgomery/Karatsuba, measurement adders), with precise counted/omitted scope in the
`secp256k1_scalarMul_toffoli_refined` docstring. **Tiered reconciliation to the literature (2026-06-22):**
a documented cost model (verified multiplier `2n²` composed with documented EFD per-op profile, squaring
`n²`, windowing, measurement-adder halving) gives three figures — verified-unoptimised `6.0×10^8`
(`secp256k1ToffoliRefined`) → windowing+squaring `2.3×10^8` (`secp256k1ToffoliWindowed`) → all standard
optimisations incl. Gidney measurement adders `1.1×10^8` (`secp256k1ToffoliOptimized`), the last
**consistent with the optimised literature ~10^8**. Verification status is explicit per tier: the
multiplier and plain double-and-add bound are VERIFIED; squaring-`n²`, windowing, and the measurement-adder
halving are DOCUMENTED (the last not formalisable in the measurement-free DSL). The honest defensible
verified number is `6.0×10^8`; the `1.1×10^8` is the cost-model reconciliation, factor-by-factor cited.
**Honest claim: a sorry-free semantic + resource scaffold for ECDLP over secp256k1**
(O(n³) structure), NOT a verified attack — the concrete reversible EC-addition circuit (fixing `M`),
`p`-primality, and a concrete on-curve point are named residue.** The build blocker is resolved.

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
CsdLean4/Mathlib/QuantumInfo/Reversible/Cost.lean      -- Tranche 1b: Cost record + circuitCost + comp lemmas  [DONE 2026-06-19, GREEN]
CsdLean4/Mathlib/QuantumInfo/Reversible/ModAdd.lean    -- Tranche 2 Pass 1: regVal + verified fullAdder + ripple cost  [DONE 2026-06-19, GREEN]
CsdLean4/Mathlib/QuantumInfo/Reversible/ModMul.lean    -- Tranche 3 Stage A: ZMod mulConst spec + shift-and-add multiplier cost  [DONE 2026-06-20, GREEN]
CsdLean4/Mathlib/QuantumInfo/Reversible/ModInv.lean    -- Tranche 4: modInv oracle + algebra + reversibility link  [DONE 2026-06-21, GREEN]
CsdLean4/Mathlib/QuantumInfo/ECDLP/EllipticCurve.lean  -- Tranche 5: scalarMul [k]P + ECDLP statement (wrap WeierstrassCurve)  [DONE 2026-06-21, GREEN]
CsdLean4/Mathlib/QuantumInfo/ECDLP/ScalarMul.lean      -- Tranche 6: doubleAndAdd [k]P + correctness + O(log k) cost  [DONE 2026-06-21, GREEN]
CsdLean4/Mathlib/QuantumInfo/ECDLP/Secp256k1.lean      -- Tranche 7: secp256k1 curve params  [DONE 2026-06-21, GREEN]
CsdLean4/Mathlib/QuantumInfo/ECDLP/ResourceBounds.lean -- Tranche 7 capstone: end-to-end Toffoli estimate  [DONE 2026-06-21, GREEN]
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

**1b — `Cost.lean` (DONE 2026-06-19, GREEN, 0 sorry, 0 warnings):** `structure Cost` (qubits,
ancilla, toffoli, toffoliDepth, cnot, tCount, meas, all ℕ; `deriving DecidableEq, Repr`);
`gateCost : Gate n → Cost` (X→0; CX→cnot 1; CCX→toffoli 1, toffoliDepth 1; swap→cnot 3);
`circuitCost c` field-wise via `(c.map (fun g => (gateCost g).field)).sum` (avoids needing an
`AddMonoid Cost` instance — correct, since `qubits`/`ancilla` are NOT additive), with `qubits := n`,
`ancilla := 0`; `circuitCost_nil`/`_qubits`/`_ancilla` simp lemmas. Comp lemmas, all proved:
`cost_comp_toffoli_count` + `cost_comp_cnot_count` (`= +`, via `List.map_append`+`List.sum_append`),
`cost_comp_toffoli_depth_le` (`≤ +`, holds with equality — `≤` is the downstream-relevant bound),
`cost_comp_qubits_le` (`≤ max`, = `n ≤ max n n` at the Pass-1 model; width/ancilla accounting is a
Pass-2 refinement, documented), plus `cost_inverse_{toffoli,cnot}` (cost invariant under
`inverse = List.reverse`, via `List.map_reverse`+`List.sum_reverse`). Both modules wired into
`CsdLean4.lean` and AxiomAudit-pinned (`denoteGate_involutive`, `reversible_inverse_correct`,
`denote_bijective`, `cost_comp_toffoli_count`, `cost_comp_toffoli_depth_le`; + the tranche-1
A1 `cfc_integral_commute`/`isClosed_posSemidef`), foundational-triple-only.

**Tranche 1 auditor pass (csd-lean-auditor, 2026-06-19): SOUND.** No Blocker/Major/Minor logical
defects; involutions genuine on the non-degenerate Bool-xor branches (probed), cost genuinely
derived (varies with the gate list, not constant), all axiom footprints match the pins. Two NITs,
both addressed: (A) degenerate gate is `denote`-identity but still billed `gateCost` — documented in
`gateCost`'s docstring as the conservative (upper-bound, syntactic) convention; (B) added a pin for
`reversible_inverse_correct'` (the surjectivity input to `denote_bijective`) for drift insurance.

## Tranche 2 status — `ModAdd.lean` (Pass 1)

**Pass 1 DONE 2026-06-19, GREEN, 0 sorry, 0 warnings; auditor-reviewed SOUND.** Built by
csd-lean-expert, verified, wired, pinned.
- **Register encoding:** `regVal : State n → ℕ` little-endian (`∑ i, if s i then 2^i else 0`);
  `regVal_lt_two_pow` (real induction, top-wire split); `regVal_update_eq` (the `Function.update`
  round-trip helper for ModMul/ScalarMul, ℕ-truncated-subtraction-correct).
- **Verified full adder:** `fullAdder a b cin cout := [CCX a b cout, CX a b, CCX cin b cout, CX cin b]`
  with `fullAdder_correct` — **genuine all-inputs coverage** (`decide` over `Fintype (Fin 4 → Bool)`,
  16 inputs, `cout` init `false`): `b ← a⊕b⊕cin`, `cout ← majority(a,b,cin)`, `a`/`cin` preserved.
  `majority` is the real 2-of-3. Derived cost `fullAdder_cost` (toffoli 2, toffoliDepth 2, cnot 2).
- **Ripple cost (general n):** `rippleAdder` (slice-list `flatMap` of `fullAdder`); `rippleAdder_toffoli`
  / `_cnot` = `2 * slices.length`, by induction composing Tranche-1's `cost_comp_{toffoli,cnot}_count`
  + `fullAdder_{toffoli,cnot}` — derived, not annotated.
- AxiomAudit-pinned (`regVal_lt_two_pow`, `regVal_update_eq`, `fullAdder_correct`, `fullAdder_cost`,
  `rippleAdder_toffoli`, `rippleAdder_cnot`); foundational-triple-only (cost lemmas `[propext]` /
  `[propext, Quot.sound]`).

**Pass 2 Stage A DONE 2026-06-19, GREEN, auditor-SOUND** (the localisation primitive + general adder):
- `Circuit.lean`: `gateWires` (wires a gate touches) + `denoteGate_apply_of_not_mem` (untouched wire
  preserved, single gate) + `denote_apply_of_forall_not_mem` (circuit frame lemma, per-gate form).
- `ModAdd.lean`: `fullAdder_apply_of_ne` (gadget touches only `{a,b,cin,cout}`) + `fullAdder_correct_general`
  — the full-adder correctness over ARBITRARY distinct `Fin n` wires (sum = `a⊕b⊕cin` to `b`, carry =
  `majority` to `cout`, `a`/`cin` preserved), lifting the concrete `State 4` `fullAdder_correct`. Proved
  by `simp_all [denoteGate]` + `cases`/`decide` on the bits; auditor confirmed genuinely general (n=6
  non-canonical-wire probe), `hc0 : s cout = false` load-bearing, not vacuous. AxiomAudit-pinned,
  foundational-triple-only. (Same commit: fixed pre-existing axiom-pin drift on `cost_comp_toffoli_depth_le`,
  now `[propext]`; the `Finset` import added to `Circuit.lean` dropped its `Quot.sound` dependency.)

**Pass 2 Stage B DONE 2026-06-20, GREEN, auditor-SOUND** (the carry-chain arithmetic correctness):
- `regValRange f s k` (ℕ-indexed low-`k` register readout) + `regValRange_succ` + `regValRange_lt` (`< 2^k`).
- `fulladder_nat` (per-slice ℕ identity: `sum + 2*carry = a+b+c`, axiom-free).
- `structure RippleLayout m n` — wire families `A B C : ℕ → Fin m` with pairwise-disjointness + bounded
  injectivity (hypotheses are pure `Fin m` WIRE geometry; the auditor confirmed no smuggled computation).
- `rippleSlice`/`ripplePrefix`/`rippleCirc` + `denote_ripplePrefix_succ`.
- `rippleCirc_invariant` — the 4-clause carry invariant (P1 carry arithmetic, P2 A untouched, P4 high-B
  preserved, P5 high-C preserved), induction on slices, lifting `fullAdder_correct_general` through
  `fullAdder_apply_of_ne` (the frame lemma).
- **`rippleCirc_correct`** (HEADLINE): `regValRange L.B (denote (rippleCirc L) s) n = (regValRange L.A s n
  + regValRange L.B s n) % 2^n`, derived from the exhibited circuit. Foundational-triple-only, AxiomAudit-pinned.
- `rippleLayout2` (concrete 2-bit layout on `Fin 7`) + `example` — non-vacuity witness. Auditor ran
  end-to-end probes: A=2,B=1→3; A=3,B=3→2 (carry-out wire genuinely set, `mod 2^n` truncation real).

**Tranche 3 next (`ModMul.lean`):** the Shor `mulOracle` target, consuming `rippleCirc_correct` +
`regVal`/`regValRange`. Auditor flagged the load-bearing risk one layer up: a shifted/reused-register
adder layout must keep `RippleLayout`'s injectivity bounds (`hCinj` on `< n+1` especially)
dischargeable — that is where vacuity could silently re-enter.

## Tranche 3 status — `ModMul.lean` (modular multiplication)

**Stage A DONE 2026-06-20, GREEN, auditor-SOUND** (semantic target + derived multiplier cost):
- `mulConst N a : ZMod N → ZMod N := (a * ·)` — the Shor `mulOracle` action; `mulConst_bijective`
  (`IsUnit a` ⇒ permutation, the reversibility that admits a circuit; auditor confirmed the unit
  hypothesis load-bearing — `mulConst 4 2` is not injective).
- `multiplier (adders : List (Circuit m)) := adders.flatMap id` — shift-and-add multiplier as the
  concatenation of partial-product adder blocks; `multiplier_toffoli`/`_cnot` = list-sum of block
  counts (DERIVED via `cost_comp_*`, not annotated).
- `ripplePrefix_toffoli`/`rippleCirc_toffoli` (a block = `2·n` Toffolis) + `multiplier_ripple_toffoli`
  (`m'` width-`n` blocks = `2·n·m'`). Honest: cost is layout-independent (syntactic) — a cost
  statement, not correctness. AxiomAudit-pinned (`[propext, Quot.sound]`).
- Per-step correctness is `ModAdd.rippleCirc_correct` (one shifted add); building block in hand.

**Stage B.1 DONE 2026-06-20, GREEN, auditor-SOUND** (the per-step accumulation correctness — the heart):
- `regValRange_split` — split a register readout at offset `i` (`low + 2^i · window`); the tool relating
  a windowed add to the full accumulator value (no division).
- `rippleCirc_preserves_external` — a ripple circuit preserves any wire disjoint from its layout (the
  frame lemma at circuit granularity; bounds `k<w` / `k<w+1` on the used wire range).
- `accStep` — **THE per-step heart**: one full-remaining-width ripple add of the multiplicand (value
  `Yv`) into the accumulator window `Acc[i, W)` increases the FULL accumulator value by exactly `2^i · Yv`
  (carry propagates through the whole upper accumulator; low `i` bits preserved; `hno` no-overflow drops
  the `rippleCirc_correct` mod). Auditor cross-checked the arithmetic two ways (lemma vs kernel circuit
  eval, both = 5 on a concrete `Fin 8` instance), `hno` load-bearing, hypotheses jointly satisfiable.
  AxiomAudit-pinned, foundational-triple-only.

**Stage B.2 DONE 2026-06-21, GREEN, auditor-SOUND** (the fold to `Acc = a·Y`):
- `structure MulLayout M n W` — accumulator `Acc`, multiplicand `Y` (W-wire register, high bits held
  zero, so no separate addend-pad wires), per-shift carry chain `Carry`. **BOUNDED injectivity/cross
  fields** (`hCarryInj` index `≤ W`, `hCarryCross` `sh,sh' ≤ W`) — an earlier UNBOUNDED version was
  UNINHABITABLE (injective ℕ→Fin M impossible), which would have made the theorem vacuous; bounding
  fixed it.
- `stepLayout` (per-shift `RippleLayout`, A = Y, B = `Acc(sh+·)`, C = `Carry sh`) + `mulCircuit`
  (concatenation of per-shift ripple adds). Each step at its own width `W - sh`, applied individually
  (the circuits are all `Circuit M`), so NO dependent-width fold needed.
- `stepLayout_preserves_Y` (multiplicand preserved: in-window A read-only via `rippleCirc_invariant`
  P2, out-of-window via the frame lemma) + `stepLayout_preserves_carry` (other shifts' carries
  preserved, via `hCarryCross`) — the two preservation properties the fold threads.
- **`mulCircuit_correct`** (HEADLINE): `regValRange Acc (denote (mulCircuit L shifts) s) W =
  regValRange Acc s W + (∑ 2^sh)·Yv`, induction over shifts folding `accStep`, re-establishing
  carries-fresh + Y-preserved + bound per recursive step. Foundational-triple-only.
- `mulLayout1 : MulLayout 6 1 1` + `example` — non-vacuity witness (`Carry sh k = 2+2·min sh 1+min k 1`,
  all 7 fields by `omega`/`decide`). Auditor independently built a 2-shift witness and ran multiply-by-3
  → 3, multiply-by-1 → 1, multiply-by-0 → 0; confirmed `hno` load-bearing.

**Stage B.3 DONE 2026-06-21, GREEN, auditor-SOUND** (the modular `ZMod N` capstone):
- `mulCircuit_correct_zmod` — the output register, cast to `ZMod N`, equals `mulConst N (∑2^sh) Y` =
  Shor's `mulOracle` action `y ↦ a·y mod N`. The `ZMod N` cast performs the reduction; the no-overflow
  hypothesis keeps the register holding the EXACT integer `a·Y` (so the cast reduces it honestly). N is
  a free `ℕ` — NO `N = 2^W` assumption (auditor instantiated at N=3, N=0; confirmed `↑3 = 1` in ZMod 2,
  the cast genuinely reduces). Foundational-triple, AxiomAudit-pinned. + a concrete `ZMod` example.
- **Honest residue (NOT built, named):** the register physically holds the exact integer `a·Y` (W bits,
  `W ≥ 2·bitlen N`); reducing it in place to a `bitlen N`-bit representative of `a·y mod N` is a
  reversible conditional-subtract modular-reduction circuit (qubit-count optimisation). That is the
  natural Stage C / next-tranche content if a space-optimal mulOracle register is wanted; the modular
  *oracle action* is already realised by B.3.

## Resume checklist
0. ~~Clear the `lake.exe` Application Control block~~ **DONE (SAC off).**
1. ~~Build `Circuit.lean`; fix the involution proofs~~ **DONE 2026-06-19 (4 fixes, green, committed).**
2. ~~Write + build `Cost.lean`~~ **DONE 2026-06-19 (green, first build).**
3. ~~Add modules to `CsdLean4.lean`; add AxiomAudit pins~~ **DONE 2026-06-19** (Circuit/Cost/ModAdd
   all in `CsdLean4.lean`; Reversible + A1 + ModAdd pins in `Tests/AxiomAudit.lean`).
4. ~~Audit (csd-lean-auditor)~~ **DONE 2026-06-19 — Tranche 1 + Tranche 2 both SOUND** (auditor pass
   is now standard per tranche).
5. ~~Commit Tranche 1; Tranche 2 Pass 1; update docs~~ **DONE 2026-06-19.**
6. ~~Tranche 2 Pass 2 Stage A (localisation lemma + general adder)~~ **DONE 2026-06-19, auditor-SOUND, committed `2ba2a2f`.**
7. ~~Tranche 2 Pass 2 Stage B (carry-chain `(A+B) mod 2^n` correctness)~~ **DONE 2026-06-20, auditor-SOUND.**
   Tranche 2 is now COMPLETE (cost + full computational correctness).
8. ~~Tranche 3 Stage A (`ModMul.lean`: `mulConst` spec + multiplier cost)~~ **DONE 2026-06-20, auditor-SOUND.**
9. ~~Tranche 3 Stage B.1 (per-step `accStep` accumulation correctness)~~ **DONE 2026-06-20, auditor-SOUND.**
10. ~~Tranche 3 Stage B.2 (fold to `Acc = a·Y` + `MulLayout` witness)~~ **DONE 2026-06-21, auditor-SOUND.**
11. ~~Tranche 3 Stage B.3 (modular `ZMod N` capstone `mulCircuit_correct_zmod`)~~ **DONE 2026-06-21,
    auditor-SOUND. TRANCHE 3 COMPLETE** (cost + correctness + modular oracle-action connection).
12. ~~Tranche 4 (`ModInv.lean`) — modular-inverse semantic layer~~ **DONE 2026-06-21, auditor-SOUND.**
    `modInv` oracle + algebra (involution, coprime bridge) + reversibility link to Tranche 3
    (`mulConst a` undone by `mulConst a⁻¹`). REUSE-only; no inversion circuit (ECDLP avoids via
    projective coords) — honest residue named.
13. ~~Tranche 5 (`ECDLP/EllipticCurve.lean`) — wrap Mathlib `WeierstrassCurve.Affine.Point`~~ **DONE
    2026-06-21, auditor-SOUND.** `scalarMul [k]P` + structural algebra + ECDLP statement; group law
    reused (not reproved). Note: needs `[DecidableEq F]` (Mathlib's `AddCommGroup W.Point` instance).
14. ~~Tranche 6 (`ECDLP/ScalarMul.lean`) — double-and-add for `[k]P`~~ **DONE 2026-06-21, auditor-SOUND.**
    `doubleAndAdd` (binary recursion) + correctness `doubleAndAdd_eq_nsmul`/`_eq_scalarMul` (closes the
    loop to Tranche-5 `scalarMul`; auditor verified it COMPUTES `k•P` at concrete values, non-circular)
    + DERIVED logarithmic cost `doubleAndAddCost_le ≤ 2·Nat.size k` (exact `= size + popcount`; O(log k),
    the first resource factor). General `AddMonoid M` (applies to `W.Point`).
15. ~~Tranche 7 (`ECDLP/Secp256k1.lean` + `ECDLP/ResourceBounds.lean`) — capstone~~ **DONE 2026-06-21,
    auditor-SOUND. PROGRAMME COMPLETE (7/7).** secp256k1 curve params + the end-to-end
    `secp256k1_scalarMul_toffoli_bound` (`O(256³)·M` Toffolis), composing T6's O(log k) op count + T3's
    `2n²` multiplier. Honest scaffold (O(n³) structure), not a verified attack.

## Residue / possible follow-ups (named, NOT built — beyond the Pass-1 scaffold)

- **The concrete reversible EC point-addition circuit** — composing the Tranche-3/4 modular-arithmetic
  oracles into the secant–tangent addition formula (projective/Jacobian coords to avoid per-op inversion).
  This is what would turn the parameter `M` (field-mults per point op) into a DERIVED Toffoli count, and
  is the natural next tranche if the scaffold is to become an absolute cost. Auditor's caveat: it must
  also cost the quantum×quantum products in the formula (the scaffold assumes quantum×classical).
- `p`-primality of secp256k1's `p` (citable fact; infeasible in Lean without an ECPP/Pratt certificate).
- A concrete on-curve `Nonsingular` point witness (lets `doubleAndAdd` run on a real EC point; needs the
  field structure, gated on `Fact p.Prime`).
- Optional ModMul Stage C: the in-place conditional-subtract register reduction (a qubit optimisation —
  a space-optimal mulOracle register vs the current exact-integer one).

---

# PHASE 2 — hardening the resource estimate (plan, 2026-06-22)

**Status: PLANNED.** Phase 1 (the 7-tranche programme) is COMPLETE: a sorry-free scaffold with the
secp256k1 tiered figures (`6.0×10^8` verified → `1.1×10^8` all-optimised, matching the literature). Phase 2
moves the estimate from "verified component + documented optimisations" toward a **verified, complete,
multi-metric** resource estimate. Each stage states its verification-status delta (documented → verified,
or component → complete) and is its own auditor-checked tranche. Effort/value below; recommended order S1
→ S4 → S2/S3 → S5 → S6.

## S1 — Depth + space (qubit) accounting [HIGHEST VALUE, novel; recommended first]

**S1 framework DONE 2026-06-22, GREEN, auditor-SOUND** (`Depth.lean`): the layered-circuit depth model.
`LayeredCircuit`/`denoteLayered`/`flatten`/`depth`; the two bridges `denoteLayered_eq_denote_flatten`
(correctness inherited from the flat model — auditor confirmed non-circular) and `layeredToffoli_eq`
(verified gate counts carry over); `LayerWF` (wire-disjoint layer = genuinely parallel; disjointness
load-bearing); `sequential` (gate-per-layer) + `rippleCirc_sequential_depth = 4n` (the ripple adder's
`O(n)` sequential depth — honestly the upper bound, carry chain inherently sequential) +
`parallelXLayer_depth = 1` (depth ≪ gate count captured for a WF parallel layer). **Remaining in S1:**
the carry-lookahead / parallel-prefix adder at `O(log n)` depth (the comparison the framework enables) +
the secp256k1 `(Toffoli, depth, qubits)` triple via composing point-op depths + tight qubit-width
accounting. Auditor's flagged trap for the continuation: any `O(log n)` layering must PROVE `LayerWF` per
layer (wire-disjoint), else the depth count is fiction.

The `Cost` struct already carries `toffoliDepth`/`qubits`/`ancilla`, but only `toffoli` is bounded; the
estimate is gate-count-only and cannot compare alternatives that trade depth/space (the regime that
matters). Deliverables:
- A **layered circuit model** (a `Circuit` as a `List` of layers, each layer a set of pairwise-wire-disjoint
  gates), `denoteLayered`, `depth := layers.length`; relate to the flat model. Parallel composition gives
  `depth = max`, the thing the flat list cannot express.
- Bound the **ripple-adder depth** `O(n)`; optionally a carry-lookahead adder at `O(log n)` depth and more
  gates — the canonical depth/gate tradeoff, and the first thing the model can then *compare*.
- **Qubit width**: track the wire count (registers + ancilla banks — already named in `RippleLayout`/
  `MulLayout`) as a function of the circuit; bound the adder/multiplier width; re-derive the secp256k1
  qubit figure (literature ~2330).
- Headline: secp256k1 as a verified `(Toffoli, depth, qubits)` triple.
- Status delta: gate-count-only → multi-metric. **Verified.** Effort: LARGE (the layered model is new;
  a verified depth/parallelism model for reversible circuits is itself a contribution).

## S2 — Verified squaring circuit [moderate]
Exhibit a squaring circuit (`~n²/2` partial products, diagonal symmetry), derive cost `= n²`. Replaces the
documented `sqrToffoli` in the tiered figures. Status delta: `sqrToffoli` documented → verified. Effort:
MODERATE (parallels the multiplier).

## S3 — Verified windowed scalar multiplication [moderate]
Define `windowedDoubleAndAdd`, prove `= k • P` (correctness) and derive its op count (`n` doublings +
`⌈n/w⌉` additions, classical precomputed table). Status delta: windowing documented → verified. Effort:
MODERATE (Tranche-6-style).

## S4 — Modular reduction, ModMul Stage C [biggest COMPLETENESS gap]
The current multiplier computes the exact integer `a·Y`; the mod-`N` reduction (omitted, ~2× per multiply)
is the largest completeness gap. Build the conditional-subtract reduction: a **subtractor** (adder with
inverted carry) + **comparison** (subtract `N`, test the borrow) + conditional add-back, proving the output
`regValRange ∈ [0, N)` and `≡ input (mod N)`. Turns the multiplier into a genuine *modular* multiplier and
the register into the space-optimal `⌈log₂ N⌉`-bit form. Status delta: component (mod `2^W`) → complete (mod
`N`). **Verified.** Effort: MODERATE-LARGE (needs subtraction + comparison circuits, both adder-class).

## S5 — Measurement-aware DSL + Gidney adder [hard, conceptually fraught]
Extend the gate DSL with a measurement gate and honest semantics (the hard part: measurement is
non-deterministic; the standard route is measure-and-classically-control the uncomputation). Define the
Gidney measurement-based adder; verify cost `= n` Toffoli (1/bit). Moves the measurement-adder 2× factor
documented → verified, making the `1.1×10^8` optimised figure a verified bound rather than a cost model.
Status delta: the optimised tier documented → verified. Effort: LARGE + conceptually fraught (measurement
semantics in a so-far-deterministic framework; risk to DSL integrity if done carelessly — do it as a
separate measurement layer, not by polluting `denoteGate`).

## S6 — Concrete EC point-addition circuit [largest; derives M]
Compose the Tranche-3/4 modular oracles into the projective/Jacobian addition + doubling formulas; prove
they compute the Mathlib group law (`+` on `W.Point`); derive `M` (the `7`/`11` field-mult counts, now
verified). Needs **quantum × quantum** modular multiplication (squaring + general products, NOT the
quantum×classical `mulConst`) and the full formula correctness. Status delta: `M` documented → derived; the
EC layer scaffold → real circuit. Effort: VERY LARGE (multi-tranche).

## Recommended start
**S1 (depth + space).** Highest value (multi-metric, comparison-enabling, matches how the literature
reports), conceptually novel (layered model), and self-contained (no dependency on S4–S6). First concrete
step: define the layered circuit + `depth`, and prove the ripple adder's `O(n)` depth bound.
