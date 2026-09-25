# The magic layer (candidate 5) — scoping and execution

**Status:** scoped and **EXECUTED 2026-08-29, same session as the GK completion** (author
instruction: "Complete GK then 5").

**Provenance.** Candidate 5 of the five from the 2026-08-28 algorithms discussion — the last
one. The pitch, verbatim: *"Magic state distillation. The other half of the Clifford story —
what you need beyond Clifford for universality. Finite-dimensional, and it leans on your POVM
and stabiliser machinery. Pairs naturally with (3)."*

## What was formalised, and the honest boundary

The session scope ran first and split the candidate the same way AA-5 was split: the
**mathematics of magic** (what provably escapes the Clifford closure, and the resource state)
is one session; **distillation protocols** are not.

`Mathlib/QuantumInfo/Magic.lean` (Cat-1, CSD-free):

* **The phase layer**: `tPhase = e^{iπ/4}` with `tPhase² = i` (`tPhase_sq`, via
  `Complex.exp_pi_div_two_mul_I`) and the closed values `e^{±iπ/4} = (1 ± i)/√2`.
* **The hierarchy descends**: `T² = S` (`tGate_tGate`) — the square of the non-Clifford gate
  is the Clifford phase gate.
* ★ **The level-3 hierarchy identity** (`tGate_conj_X`): `T X T† = (X + i·XZ)/√2` — an exact
  operator identity: conjugation by `T` carries the Pauli `X` out of the Pauli family but
  into its two-term span, i.e. into the Clifford group's territory. GK-2 proved H, S, CNOT
  stay level-2; this is what level-3 looks like.
* ★★ **The no-go** (`tGate_conj_X_not_pauli`): there are **no** `c, a, b` with
  `T X T† = c·X^a Z^b`. Pinning the two basis columns forces `1 = ±i`. Together with GK-2
  this brackets the boundary of the Gottesman–Knill mechanism from both sides — the
  Clifford generators provably close over the Paulis, `T` provably escapes.
* **The magic state** `|T⟩ = T·H|0⟩` (`magicState`), coordinates `(1, e^{iπ/4})/√2`
  (`magicState_apply`), unit norm (`inner_magicState_self`).

## Named residues (not attempted, with reasons)

* **Distillation** (Bravyi–Kitaev 15-to-1, or any threshold statement): **built 2026-09-24**
  across four modules (BACKLOG #75–#78) — `ReedMuller15.lean` (the code's combinatorics),
  `ReedMuller15Code.lean` (transversal `T` = logical `T†`), `ReedMuller15Errors.lean` (detection
  and the logical `Z̄`), `ReedMuller15Distill.lean` (the `35 p³` bound and the recursion);
  R-004 closed. The explicit decoder circuit is #79.
* **Universality** (Clifford+T dense in SU(2ⁿ)): a gate-synthesis density theorem
  (Solovay–Kitaev territory), out of scope for the coordinate-operator corpus.
* **The T-injection circuit** (consuming `|T⟩` implements `T` with Clifford + measurement):
  **built 2026-09-23** as `MagicInjection.lean` (BACKLOG #66–#67): the pure-state identity
  `injectSlice_magicState`, the channel `injectionChannel_apply`, the noisy resource
  `noisyInjectionChannel_apply`; R-006 closed.

No priority claim of any kind (CL-061 rule).

## Execution record — 2026-08-29

GK completion (measurement-update + rank/uniqueness, `Stabilizer.lean` +~230 lines) and
`Magic.lean` (~290 lines) together ≈ 110 minutes wall-clock including build iterations.
Snags for the pile: `decide` cannot take a goal with free variables — apply a
`∀`-quantified decide-fact instead (`rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) u`);
a `simp` that beta-reduces coordinate applications turns `(fun _ => 1) 0`-shaped rewrite
targets into bare literals, so write the post-`simp` shows against the reduced form; after
an `← h22`-style rewrite of `2`, every other `2` in the goal mutates too — prove the
`√2/2 = (√2)⁻¹` bridge as a standalone lemma with `field_simp` instead.

## The split (2026-09-23): BACKLOG #15 → #66–#79

Author instruction: "break up 15 so it's not so big". R-006 closed 2026-09-23 (#67) and R-004 closed 2026-09-24 (#78); R-005 stays open in
`residues.tsv` until its closing row lands (#73); each row is a self-contained brick in the corpus's
coordinate-operator model (`QReg n`, `pauliOp`, `cnotGate`/`sGate`/`hGate`/`tGate`,
`stabProjector`/`measProj`, `Channel` with Kraus operators, the pattern measure of
`CodeCapacityThreshold.lean`). The XL / XL / L of the unsplit row were the prices of the unsplit
objects; nothing below is above M–L except #74, which the chain does not need.

| Residue | Row | Brick | Price | Needs |
|---|---|---|---|---|
| R-006 | #66 | T-injection, pure-state form (and the `Z`-error transfer) — **built 2026-09-23**, `MagicInjection.lean` | S–M | — |
| R-006 | #67 | T-injection as a channel: `R.apply ρ = T ρ T†` — **built 2026-09-23, R-006 closed** (`injectionChannel_apply`) | M | #66, `Channel.lean` |
| R-005 | #68 | the `HT` rotation angle is an irrational multiple of `π` (algebraic-integer argument); dense powers | M | Mathlib: `IsPrimitiveRoot.isIntegral`, `IsIntegrallyClosed ℤ`, `AddCircle.denseRange_zsmul_coe_iff` |
| R-005 | #69 | `⟨H, T⟩` dense in `U(2)` mod phase (Euler decomposition for two non-parallel axes) | M–L | #68 |
| R-005 | #70 | every `d × d` unitary is a product of two-level unitaries | M | — |
| R-005 | #71 | a two-level unitary = Gray-code CNOTs + one `C^{n−1}(U)` | M | #70 |
| R-005 | #72 | `C^k(U)` from CNOT and single-qubit gates | M–L | #71, `Reversible/Lift.lean` |
| R-005 | #73 | Clifford+T dense in `U(2ⁿ)` mod phase — closes R-005 | S–M | #69, #72, the telescoping bound |
| R-005 | #74 | Solovay–Kitaev efficiency — not needed by the chain, not claimed | XL | #73 |
| R-004 | #75 | `[[15, 1, 3]]` combinatorics: undetected `Z`-patterns have weight `≥ 3`, exactly `35` of weight `3`, odd weight = logical — **built 2026-09-23**, `ReedMuller15.lean` | S–M | — |
| R-004 | #76 | transversal `T` = logical `T†` (weights `0/8` and `7/15`) — **built 2026-09-23**, `ReedMuller15Code.lean` | M | #75 |
| R-004 | #77 | `Z_e T^{⊗15}|+̄⟩`: detected by the `X`-checks iff `syndrome e ≠ 0`, otherwise `Z̄^{[e]}|Ā'⟩` (restated 2026-09-23 — the protocol injects `T` into the encoded `|+̄⟩`; the earlier 'project fifteen bare magic states' picture has acceptance `2^{−10}` and was wrong) — **built 2026-09-23**, `ReedMuller15Errors.lean` | M | #76, #66–#67 |
| R-004 | #78 | the `35 p³` bound and the cube recursion — **built 2026-09-24, R-004 closed** (`distillation_error_le`, `tendsto_distillIter`) | M–L | #75, #77 |
| R-004 | #79 | the decoder as an explicit Clifford circuit | M | #78 |

Three independent roots (#66; #68 and #70; #75); the longest chain is #70 → #71 → #72 → #73.
The doc's link 12 keeps saying what exists (the `T` gate and its escape from Clifford) until the
closing rows land.

## References

Gottesman–Chuang teleportation-gate hierarchy (Nature 402, 390 (1999)); Bravyi–Kitaev,
"Universal quantum computation with ideal Clifford gates and noisy ancillas"
(PRA 71, 022316 (2005)); Nielsen–Chuang §10.6.2 (the π/8 gate and fault tolerance).
In-corpus: `Clifford.lean` (GK-2, the closure this module complements), `Stabilizer.lean`
(GK-3 + measurement), `specs/gottesman-knill-plan.md`.
